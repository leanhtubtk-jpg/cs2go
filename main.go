// main.go
package main

import (
	"encoding/json"
	"fmt"
	"log"
	"math"
	"os"
	"runtime"
	"strings"
	"syscall"
	"time"
	"unicode"
	"unsafe"

	"github.com/lxn/win"
	"github.com/ttacon/chalk"
	"golang.org/x/sys/windows"
)

type Matrix [4][4]float32
type Vector3 struct{ X, Y, Z float32 }
type Vector2 struct{ X, Y float32 }
type Rectangle struct{ Top, Left, Right, Bottom float32 }

type Entity struct {
	Health   int32
	Team     int32
	Name     string
	Position Vector2
	Bones    map[string]Vector2
	HeadPos  Vector3
	Distance float32
	Rect     Rectangle
}

type Offset struct {
	DwViewMatrix           uintptr `json:"dwViewMatrix"`
	DwLocalPlayerPawn      uintptr `json:"dwLocalPlayerPawn"`
	DwEntityList           uintptr `json:"dwEntityList"`
	M_hPlayerPawn          uintptr `json:"m_hPlayerPawn"`
	M_iHealth              uintptr `json:"m_iHealth"`
	M_lifeState            uintptr `json:"m_lifeState"`
	M_iTeamNum             uintptr `json:"m_iTeamNum"`
	M_vOldOrigin           uintptr `json:"m_vOldOrigin"`
	M_pGameSceneNode       uintptr `json:"m_pGameSceneNode"`
	M_modelState           uintptr `json:"m_modelState"`
	M_boneArray            uintptr `json:"m_boneArray"`
	M_nodeToWorld          uintptr `json:"m_nodeToWorld"`
	M_sSanitizedPlayerName uintptr `json:"m_sSanitizedPlayerName"`
}

// === GDI & System DLL ===
var (
	user32                     = windows.NewLazySystemDLL("user32.dll")
	gdi32                      = windows.NewLazySystemDLL("gdi32.dll")
	getSystemMetrics           = user32.NewProc("GetSystemMetrics")
	setLayeredWindowAttributes = user32.NewProc("SetLayeredWindowAttributes")
	showCursor                 = user32.NewProc("ShowCursor")
	setTextAlign               = gdi32.NewProc("SetTextAlign")
	createFont                 = gdi32.NewProc("CreateFontW")
	createCompatibleDC         = gdi32.NewProc("CreateCompatibleDC")
	createSolidBrush           = gdi32.NewProc("CreateSolidBrush")
	createPen                  = gdi32.NewProc("CreatePen")
)

// === ESP Settings ===
var (
	teamCheck           = true
	headCircle          = true
	skeletonRendering   = true
	boxRendering        = true
	nameRendering       = true
	healthBarRendering  = true
	healthTextRendering = true

	// FPS Control (từ C++)
	desiredFrameRate = 60
	frameDelay       uint32
	lastFrameTime    time.Time
)

func init() {
	runtime.LockOSThread()
	frameDelay = uint32(1000 / desiredFrameRate)
	lastFrameTime = time.Now()
}

// === Helper Functions ===
func (v Vector3) Dist(o Vector3) float32 {
	return float32(math.Abs(float64(v.X-o.X)) + math.Abs(float64(v.Y-o.Y)) + math.Abs(float64(v.Z-o.Z)))
}

func logAndSleep(msg string, err error) {
	log.Printf("%s: %v\n", msg, err)
	time.Sleep(5 * time.Second)
}

func worldToScreen(m Matrix, pos Vector3) (float32, float32) {
	x := m[0][0]*pos.X + m[0][1]*pos.Y + m[0][2]*pos.Z + m[0][3]
	y := m[1][0]*pos.X + m[1][1]*pos.Y + m[1][2]*pos.Z + m[1][3]
	w := m[3][0]*pos.X + m[3][1]*pos.Y + m[3][2]*pos.Z + m[3][3]
	if w < 0.01 {
		return -1, -1
	}
	inv := 1.0 / w
	x *= inv
	y *= inv

	width, _, _ := getSystemMetrics.Call(0)
	height, _, _ := getSystemMetrics.Call(1)
	wf := float32(width)
	hf := float32(height)

	return wf/2 + 0.5*x*wf + 0.5, hf/2 - 0.5*y*hf + 0.5
}

func getOffsets() Offset {
	data, err := os.ReadFile("offsets.json")
	if err != nil {
		logAndSleep("Cannot read offsets.json", err)
		return Offset{}
	}
	var o Offset
	json.Unmarshal(data, &o)
	return o
}

func read(h windows.Handle, addr uintptr, v any) error {
	_, err := windows.ReadProcessMemory(h, addr, (*byte)(unsafe.Pointer(&v)), unsafe.Sizeof(v), nil)
	return err
}

// === Entity Reading ===
func getEntitiesInfo(ph windows.Handle, base, sw, sh uintptr, off Offset) []Entity {
	var entities []Entity
	var list uintptr
	if read(ph, base+off.DwEntityList, &list) != nil { return entities }

	var localP, localScene, localOrigin Vector3
	var localTeam int32
	var viewMatrix Matrix

	read(ph, base+off.DwLocalPlayerPawn, &localP)
	read(ph, localP+off.M_pGameSceneNode, &localScene)
	read(ph, localScene+off.M_nodeToWorld, &localOrigin)
	read(ph, base+off.DwViewMatrix, &viewMatrix)

	bones := map[string]int{
		"head": 6, "neck_0": 5, "spine_1": 4, "spine_2": 2, "pelvis": 0,
		"arm_upper_L": 8, "arm_lower_L": 9, "hand_L": 10,
		"arm_upper_R": 13, "arm_lower_R": 14, "hand_R": 15,
		"leg_upper_L": 22, "leg_lower_L": 23, "ankle_L": 24,
		"leg_upper_R": 25, "leg_lower_R": 26, "ankle_R": 27,
	}

	for i := 0; i < 64; i++ {
		var e Entity
		boneMap := make(map[string]Vector2)
		var listEntry, controller, pawnCtrl, pawn, scene, boneArray uintptr
		var team, hp, life int32
		var origin, head, bone Vector3
		var nameAddr uintptr
		var name string
		var sb strings.Builder

		read(ph, list+uintptr((8*(i&0x7FFF)>>9)+16), &listEntry)
		if listEntry == 0 { continue }
		read(ph, listEntry+uintptr(112)*(i&0x1FF), &controller)
		if controller == 0 { continue }
		read(ph, controller+off.M_hPlayerPawn, &pawnCtrl)
		if pawnCtrl == 0 { continue }

		read(ph, list+uintptr(0x8*((pawnCtrl&0x7FFF)>>9)+16), &listEntry)
		if listEntry == 0 { continue }
		read(ph, listEntry+uintptr(112)*(pawnCtrl&0x1FF), &pawn)
		if pawn == 0 || pawn == localP { continue }

		read(ph, pawn+off.M_lifeState, &life)
		if life != 256 { continue }

		read(ph, pawn+off.M_iTeamNum, &team)
		if team == 0 { continue }
		if teamCheck {
			read(ph, localP+off.M_iTeamNum, &localTeam)
			if localTeam == team { continue }
		}

		read(ph, pawn+off.M_iHealth, &hp)
		if hp < 1 || hp > 100 { continue }

		read(ph, controller+off.M_sSanitizedPlayerName, &nameAddr)
		read(ph, nameAddr, &name)
		for _, r := range name {
			if unicode.IsLetter(r) || unicode.IsDigit(r) || unicode.IsPunct(r) || unicode.IsSpace(r) {
				sb.WriteRune(r)
			}
		}

		read(ph, pawn+off.M_pGameSceneNode, &scene)
		if scene == 0 { continue }
		read(ph, scene+off.M_modelState+off.M_boneArray, &boneArray)
		if boneArray == 0 { continue }
		read(ph, pawn+off.M_vOldOrigin, &origin)

		for name, idx := range bones {
			read(ph, boneArray+uintptr(idx)*32, &bone)
			x, y := worldToScreen(viewMatrix, bone)
			boneMap[name] = Vector2{x, y}
			if name == "head" { head = bone }
		}

		headTop := Vector3{head.X, head.Y, head.Z + 7}
		headBot := Vector3{head.X, head.Y, head.Z - 5}
		hx, hty := worldToScreen(viewMatrix, headTop)
		_, hby := worldToScreen(viewMatrix, headBot)
		fx, fy := worldToScreen(viewMatrix, origin)
		boxTop := Vector3{origin.X, origin.Y, origin.Z + 70}
		_, bty := worldToScreen(viewMatrix, boxTop)

		if hx <= -1 || fy <= -1 || hx >= float32(sw) || hty >= float32(sh) { continue }

		height := fy - bty
		e = Entity{
			Health:   hp,
			Team:     team,
			Name:     sb.String(),
			Distance: origin.Dist(localOrigin),
			Position: Vector2{fx, fy},
			Bones:    boneMap,
			HeadPos:  Vector3{hx, hty, hby},
			Rect:     Rectangle{bty, fx - height/4, fx + height/4, fy},
		}
		entities = append(entities, e)
	}
	return entities
}

// === Drawing ===
func drawSkeleton(hdc win.HDC, pen uintptr, bones map[string]Vector2) {
	win.SelectObject(hdc, win.HGDIOBJ(pen))
	lines := [][2]string{
		{"head", "neck_0"}, {"neck_0", "spine_1"}, {"spine_1", "spine_2"}, {"spine_2", "pelvis"},
		{"pelvis", "leg_upper_L"}, {"leg_upper_L", "leg_lower_L"}, {"leg_lower_L", "ankle_L"},
		{"pelvis", "leg_upper_R"}, {"leg_upper_R", "leg_lower_R"}, {"leg_lower_R", "ankle_R"},
		{"spine_1", "arm_upper_L"}, {"arm_upper_L", "arm_lower_L"}, {"arm_lower_L", "hand_L"},
		{"spine_1", "arm_upper_R"}, {"arm_upper_R", "arm_lower_R"}, {"arm_lower_R", "hand_R"},
	}
	for _, l := range lines {
		p1 := bones[l[0]]
		p2 := bones[l[1]]
		win.MoveToEx(hdc, int(p1.X), int(p1.Y), nil)
		win.LineTo(hdc, int32(p2.X), int32(p2.Y))
	}
}

func renderEntityInfo(hdc win.HDC, tPen, gPen, oPen, hPen uintptr, r Rectangle, hp int32, name string, head Vector3) {
	if boxRendering {
		win.SelectObject(hdc, win.HGDIOBJ(tPen))
		win.Rectangle(hdc, int32(r.Left), int32(r.Top), int32(r.Right), int32(r.Bottom))
		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.Rectangle(hdc, int32(r.Left)-1, int32(r.Top)-1, int32(r.Right)+1, int32(r.Bottom)+1)
	}

	if headCircle {
		rad := int32((int32(head.Z) - int32(head.Y)) / 2)
		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.Ellipse(hdc, int32(head.X)-rad-1, int32(head.Y)-1, int32(head.X)+rad+1, int32(head.Z)+1)
		win.SelectObject(hdc, win.HGDIOBJ(hPen))
		win.Ellipse(hdc, int32(head.X)-rad, int32(head.Y), int32(head.X)+rad, int32(head.Z))
	}

	if healthBarRendering {
		y := int(r.Bottom + 1 - float64(int(r.Bottom+1-int(r.Top))*float64(hp)/100.0))
		win.SelectObject(hdc, win.HGDIOBJ(gPen))
		win.MoveToEx(hdc, int(r.Left)-4, y, nil)
		win.LineTo(hdc, int32(r.Left)-4, int32(r.Bottom)+1)
		win.SelectObject(hdc, win.HGDIOBJ(oPen))
		win.Rectangle(hdc, int32(r.Left)-5, int32(r.Top)-1, int32(r.Left)-3, int32(r.Bottom)+1)
	}

	if healthTextRendering {
		text, _ := windows.UTF16PtrFromString(fmt.Sprintf("%d", hp))
		win.SetTextColor(hdc, win.RGB(0, 255, 50))
		setTextAlign.Call(uintptr(hdc), 0x00000002)
		y := int(r.Bottom + 1 - float64(int(r.Bottom+1-int(r.Top))*float64(hp)/100.0))
		if !healthBarRendering { y = int(r.Top) }
		win.TextOut(hdc, int32(r.Left)-8, int32(y), text, int32(len(fmt.Sprintf("%d", hp))))
	}

	if nameRendering {
		text, _ := windows.UTF16PtrFromString(name)
		win.SetTextColor(hdc, win.RGB(255, 255, 255))
		setTextAlign.Call(uintptr(hdc), 0x00000006)
		win.TextOut(hdc, int32(r.Left)+int32((int32(r.Right)-int32(r.Left))/2), int32(r.Top)-14, text, int32(len(name)))
	}
}

// === Window & Menu ===
func windowProc(hwnd win.HWND, msg uint32, w, l uintptr) uintptr {
	if msg == win.WM_DESTROY {
		win.PostQuitMessage(0)
		return 0
	}
	return win.DefWindowProc(hwnd, msg, w, l)
}

func initWindow(w, h uintptr) win.HWND {
	class, _ := windows.UTF16PtrFromString("cs2go")
	title, _ := windows.UTF16PtrFromString("cs2go")

	wc := win.WNDCLASSEX{
		CbSize:        uint32(unsafe.Sizeof(win.WNDCLASSEX{})),
		Style:         win.CS_HREDRAW | win.CS_VREDRAW,
		LpfnWndProc:   syscall.NewCallback(windowProc),
		HInstance:     win.GetModuleHandle(nil),
		HCursor:       win.LoadCursor(0, (*uint16)(unsafe.Pointer(uintptr(win.IDC_ARROW)))),
		HbrBackground: win.COLOR_WINDOW,
		LpszClassName: class,
	}
	win.RegisterClassEx(&wc)

	hwnd := win.CreateWindowEx(
		win.WS_EX_TOPMOST|win.WS_EX_NOACTIVATE|win.WS_EX_LAYERED|win.WS_EX_TRANSPARENT,
		class, title, win.WS_POPUP,
		0, 0, int32(w), int32(h),
		0, 0, win.GetModuleHandle(nil), nil,
	)
	setLayeredWindowAttributes.Call(uintptr(hwnd), 0, 0, 0x00000001)
	showCursor.Call(0)
	win.ShowWindow(hwnd, win.SW_SHOW)
	return hwnd
}

func cliMenu() {
	for {
		fmt.Print("\033[H\033[2J")
		fmt.Println(chalk.Magenta.Color("   ____  _____  ___  ___  "))
		fmt.Println(chalk.Magenta.Color("  / ___||___ / / _ \\/ _ \\ "))
		fmt.Println(chalk.Magenta.Color(" | |  _  |_ \\| | | | | | |"))
		fmt.Println(chalk.Magenta.Color(" | |_| |___) | |_| | |_| |"))
		fmt.Println(chalk.Magenta.Color("  \\____|____/ \\___/ \\___/ \n"))
		fmt.Println(chalk.Dim.TextStyle("\t\tby bqj - v1.7 (Go + FPS Lock)\n"))

		s := func(b bool, on, off string) string {
			if b { return chalk.Green.Color(on) } else { return chalk.Red.Color(off) }
		}
		fmt.Println(s(teamCheck, "[1] Team check [ON]", "[1] Team check [OFF]"))
		fmt.Println(s(headCircle, "[2] Head circle [ON]", "[2] Head circle [OFF]"))
		fmt.Println(s(skeletonRendering, "[3] Skeleton [ON]", "[3] Skeleton [OFF]"))
		fmt.Println(s(boxRendering, "[4] Box [ON]", "[4] Box [OFF]"))
		fmt.Println(s(healthBarRendering, "[5] Health bar [ON]", "[5] Health bar [OFF]"))
		fmt.Println(s(healthTextRendering, "[6] Health text [ON]", "[6] Health text [OFF]"))
		fmt.Println(s(nameRendering, "[7] Name [ON]", "[7] Name [OFF]"))
		fmt.Printf("%s[%d FPS → %dms]\n", chalk.Cyan.Color("[8] FPS: "), desiredFrameRate, frameDelay)
		fmt.Println(chalk.Red.Color("[9] Exit"))
		fmt.Print(chalk.Cyan.Color("Select: "))

		var in string
		fmt.Scanln(&in)
		switch in {
		case "1": teamCheck = !teamCheck
		case "2": headCircle = !headCircle
		case "3": skeletonRendering = !skeletonRendering
		case "4": boxRendering = !boxRendering
		case "5": healthBarRendering = !healthBarRendering
		case "6": healthTextRendering = !healthTextRendering
		case "7": nameRendering = !nameRendering
		case "8":
			fmt.Print(chalk.Cyan.Color("Enter FPS (30-240): "))
			var fps int
			fmt.Scanln(&fps)
			if fps >= 30 && fps <= 240 {
				desiredFrameRate = fps
				frameDelay = uint32(1000 / desiredFrameRate)
				if frameDelay < 1 { frameDelay = 1 }
			}
		case "9": os.Exit(0)
		}
	}
}

// === Process Utils ===
func findProcessId(name string) (uint32, error) {
	snap, err := windows.CreateToolhelp32Snapshot(windows.TH32CS_SNAPPROCESS, 0)
	if err != nil { return 0, err }
	defer windows.CloseHandle(snap)

	var pe windows.ProcessEntry32
	pe.Size = uint32(unsafe.Sizeof(pe))
	if windows.Process32First(snap, &pe) != nil { return 0, fmt.Errorf("no process") }

	for {
		if strings.EqualFold(windows.UTF16PtrToString(&pe.SzExeFile[0]), name) {
			return pe.ProcessID, nil
		}
		if windows.Process32Next(snap, &pe) != nil { break }
	}
	return 0, fmt.Errorf("not found")
}

func getModuleBase(pid uint32, mod string) (uintptr, error) {
	snap, err := windows.CreateToolhelp32Snapshot(windows.TH32CS_SNAPMODULE, pid)
	if err != nil { return 0, err }
	defer windows.CloseHandle(snap)

	var me windows.ModuleEntry32
	me.Size = uint32(unsafe.Sizeof(me))
	if windows.Module32First(snap, &me) != nil { return 0, fmt.Errorf("no module") }

	for {
		if strings.EqualFold(windows.UTF16PtrToString(&me.SzModule[0]), mod) {
			return uintptr(me.ModBaseAddr), nil
		}
		if windows.Module32Next(snap, &me) != nil { break }
	}
	return 0, fmt.Errorf("not found")
}

func getProcessHandle(pid uint32) (windows.Handle, error) {
	return windows.OpenProcess(windows.PROCESS_VM_READ, false, pid)
}

// === MAIN ===
func main() {
	go cliMenu()

	sw, _, _ := getSystemMetrics.Call(0)
	sh, _, _ := getSystemMetrics.Call(1)
	hwnd := initWindow(sw, sh)
	if hwnd == 0 { log.Fatal("Window failed") }

	pid, err := findProcessId("cs2.exe")
	if err != nil { logAndSleep("CS2 not found", err); return }
	base, err := getModuleBase(pid, "client.dll")
	if err != nil { logAndSleep("client.dll not found", err); return }
	ph, err := getProcessHandle(pid)
	if err != nil { logAndSleep("OpenProcess failed", err); return }
	defer windows.CloseHandle(ph)

	hdc := win.GetDC(hwnd)
	bg, _, _ := createSolidBrush.Call(0x000000)
	red, _, _ := createPen.Call(win.PS_SOLID, 1, 0x7a78ff)
	green, _, _ := createPen.Call(win.PS_SOLID, 1, 0x7dff78)
	blue, _, _ := createPen.Call(win.PS_SOLID, 1, 0xff8e78)
	bone, _, _ := createPen.Call(win.PS_SOLID, 1, 0xffffff)
	outline, _, _ := createPen.Call(win.PS_SOLID, 1, 0x000001)
	font, _, _ := createFont.Call(12, 0, 0, 0, win.FW_HEAVY, 0, 0, 0, win.DEFAULT_CHARSET, 0, 0, 0, 0, 0)

	off := getOffsets()

	var msg win.MSG
	for win.GetMessage(&msg, 0, 0, 0) > 0 {
		win.TranslateMessage(&msg)
		win.DispatchMessage(&msg)

		// === FPS CONTROL (từ C++) ===
		currentTime := time.Now()
		deltaTime := currentTime.Sub(lastFrameTime).Milliseconds()

		if deltaTime < int64(frameDelay) {
			sleepTime := int64(frameDelay) - deltaTime
			time.Sleep(time.Duration(sleepTime) * time.Millisecond)
		}
		lastFrameTime = currentTime
		// === END FPS CONTROL ===

		memDC, _, _ := createCompatibleDC.Call(uintptr(hdc))
		bitmap := win.CreateCompatibleBitmap(hdc, int32(sw), int32(sh))
		win.SelectObject(win.HDC(memDC), win.HGDIOBJ(bitmap))
		win.SelectObject(win.HDC(memDC), win.HGDIOBJ(bg))
		win.SetBkMode(win.HDC(memDC), win.TRANSPARENT)
		win.SelectObject(win.HDC(memDC), win.HGDIOBJ(font))

		entities := getEntitiesInfo(ph, base, sw, sh, off)
		for _, e := range entities {
			if e.Distance < 35 { continue }
			if skeletonRendering {
				drawSkeleton(win.HDC(memDC), bone, e.Bones)
			}
			teamPen := red
			if e.Team != 2 { teamPen = blue }
			renderEntityInfo(win.HDC(memDC), teamPen, green, outline, bone, e.Rect, e.Health, e.Name, e.HeadPos)
		}

		win.BitBlt(hdc, 0, 0, int32(sw), int32(sh), win.HDC(memDC), 0, 0, win.SRCCOPY)
		win.DeleteObject(win.HGDIOBJ(bitmap))
		win.DeleteDC(win.HDC(memDC))
	}
}
