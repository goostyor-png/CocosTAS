local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local TweenService = game:GetService("TweenService")
local UIS = game:GetService("UserInputService")
local HttpService = game:GetService("HttpService")

local lp = Players.LocalPlayer

local CFG = {
	MinScale = 0.02,
	Presets = { 1, 0.5, 0.25, 0.1, 0.05 },
	PlayMuls = { 1, 2, 4, 8 },
	DeathRewind = 2,
	TrailStep = 0.12,
	TrailMax = 500,
}

local S = {
	mode = "idle",
	scale = 1,
	paused = false,
	frames = {},
	gt = 0,
	loop = false,
	rev = false,
	pmulIdx = 1,
	cam = true,
	hud = false,
	ghostMode = 1,
	best = nil,
	bestTime = nil,
	trail = false,
	autoSave = true,
	autoRew = true,
	mA = nil,
	mB = nil,
	slot = 1,
	slots = {},
	cp = nil,
	undo = {},
	undoLegacy = {},
	legacyFrames = false,
	pv = Vector3.zero,
	pa = false,
	ar = true,
	lastState = nil,
	stepReq = 0,
	stepRemaining = 0,
	ghostFrames = nil,
	camPrev = nil,
	camFovPrev = nil,
	dead = false,
}
local conns = {}
local refreshUI, notify, refreshSaveList, finishPlayback
local menuManualVisible = true
local menuForceVisible = false
local playbackUiLocked = false
local playbackHideToken = 0

local function chr()
	local c = lp.Character
	if not c then return end
	local h = c:FindFirstChildOfClass("Humanoid")
	local r = c:FindFirstChild("HumanoidRootPart")
	if h and r then return c, h, r end
end

local function totalTime()
	local n = #S.frames
	return n > 0 and S.frames[n].t or 0
end

local function copyFrames(f) return table.move(f, 1, #f, 1, {}) end

local function snapshot()
	S.undo[#S.undo + 1] = copyFrames(S.frames)
	S.undoLegacy[#S.undoLegacy + 1] = S.legacyFrames
end

local function setControls(on)
	pcall(function()
		local ps = lp:FindFirstChild("PlayerScripts")
		local pm = ps and ps:FindFirstChild("PlayerModule")
		if not pm then return end
		local ctl = require(pm):GetControls()
		if on then ctl:Enable() else ctl:Disable() end
	end)
end

local function restoreCam()
	if S.camPrev then
		local cam = workspace.CurrentCamera
		if cam then
			pcall(function()
				cam.CameraType = S.camPrev
				if S.camFovPrev then cam.FieldOfView = S.camFovPrev end
			end)
		end
		S.camPrev = nil
		S.camFovPrev = nil
	end
end

local function sample(f, t)
	local n = #f
	if n == 0 then return end
	local lo, hi = 1, n
	while lo < hi do
		local mid = (lo + hi + 1) // 2
		if f[mid].t <= t then lo = mid else hi = mid - 1 end
	end
	local a, b = f[lo], f[lo + 1]
	local k = 0
	if b and b.t > a.t then k = math.clamp((t - a.t) / (b.t - a.t), 0, 1) end
	return a, b, k, lo
end

local function interpolate(f, t)
	local a, b, k = sample(f, t)
	if not a then return end
	if not b or k <= 0 then return a.cf, a.v, a, b, k end
	local span = math.max(b.t - a.t, 1e-5)
	local p0 = a.cf.Position
	local p1 = b.cf.Position
	local delta = p1 - p0
	local m0 = a.v * span
	local m1 = b.v * span
	local chordLength = delta.Magnitude
	if chordLength < 1e-4 then
		m0 = Vector3.zero
		m1 = Vector3.zero
	else
		local direction = delta / chordLength
		local along0 = m0:Dot(direction)
		local along1 = m1:Dot(direction)
		if along0 < 0 then m0 -= direction * along0 end
		if along1 < 0 then m1 -= direction * along1 end
		local maxTangent = chordLength * 3
		if m0.Magnitude > maxTangent then m0 = m0.Unit * maxTangent end
		if m1.Magnitude > maxTangent then m1 = m1.Unit * maxTangent end
		local alpha = m0:Dot(direction) / chordLength
		local beta = m1:Dot(direction) / chordLength
		local tangentSum = alpha * alpha + beta * beta
		if tangentSum > 9 then
			local limiter = 3 / math.sqrt(tangentSum)
			m0 *= limiter
			m1 *= limiter
		end
	end
	local k2 = k * k
	local k3 = k2 * k
	local h00 = 2 * k3 - 3 * k2 + 1
	local h10 = k3 - 2 * k2 + k
	local h01 = -2 * k3 + 3 * k2
	local h11 = k3 - k2
	local pos = p0 * h00 + m0 * h10 + p1 * h01 + m1 * h11
	local dh00 = 6 * k2 - 6 * k
	local dh10 = 3 * k2 - 4 * k + 1
	local dh01 = -6 * k2 + 6 * k
	local dh11 = 3 * k2 - 2 * k
	local velocity = (p0 * dh00 + m0 * dh10 + p1 * dh01 + m1 * dh11) / span
	local rotation = a.cf:Lerp(b.cf, k).Rotation
	return CFrame.new(pos) * rotation, velocity, a, b, k
end

local function shiftFrame(fr, dt)
	local n = {}
	for k, v in pairs(fr) do n[k] = v end
	n.t = fr.t + dt
	return n
end

local store = setmetatable({}, { __mode = "k" })
local function prop(obj, name, mult)
	local d = store[obj]
	if not d then d = {}; store[obj] = d end
	local p = d[name]
	local cur = obj[name]
	if not p then
		p = { base = cur, last = cur }
		d[name] = p
	elseif math.abs(cur - p.last) > 1e-4 then
		p.base = cur
	end
	local v = p.base * mult
	p.last = v
	obj[name] = v
end
local function unprop(obj, name)
	local d = store[obj]
	local p = d and d[name]
	if p then obj[name] = p.base; d[name] = nil end
end

local trk = setmetatable({}, { __mode = "k" })
local function trackScale(t, mult)
	local d = trk[t]
	local cur = t.Speed
	if not d then
		d = { base = cur, last = cur }
		trk[t] = d
	elseif math.abs(cur - d.last) > 1e-3 then
		d.base = cur
	end
	local v = d.base * mult
	d.last = v
	t:AdjustSpeed(v)
end

local function setParticles()
	local ts = (S.paused and S.stepReq == 0) and 0 or S.scale
	for _, d in ipairs(workspace:GetDescendants()) do
		if d:IsA("ParticleEmitter") then pcall(function() d.TimeScale = ts end) end
	end
end

local slowOn = false
local function applySlow()
	local s = S.scale
	local animPaused = S.paused and S.stepReq == 0
	local want = s < 0.999 or S.paused
	local _, h = chr()
	if want then
		slowOn = true
		prop(workspace, "Gravity", s * s)
		if h then
			prop(h, "WalkSpeed", s)
			if h.UseJumpPower then
				prop(h, "JumpPower", s)
				unprop(h, "JumpHeight")
			else
				unprop(h, "JumpPower")
			end
			local an = h:FindFirstChildOfClass("Animator")
			if an then
				for _, t in ipairs(an:GetPlayingAnimationTracks()) do
					trackScale(t, animPaused and 0 or s)
				end
			end
		end
	elseif slowOn then
		slowOn = false
		unprop(workspace, "Gravity")
		if h then
			unprop(h, "WalkSpeed")
			unprop(h, "JumpPower")
			unprop(h, "JumpHeight")
			local an = h:FindFirstChildOfClass("Animator")
			if an then
				for _, t in ipairs(an:GetPlayingAnimationTracks()) do
					local d = trk[t]
					if d then t:AdjustSpeed(d.base); trk[t] = nil end
				end
			end
		end
		setParticles()
	end
end

local function setPaused(p)
	if S.mode == "play" then
		playbackHideToken += 1
		playbackUiLocked = true
	end
	if S.paused == p then
		if refreshUI then refreshUI() end
		return
	end
	S.paused = p
	local _, _, r = chr()
	if r then
		if p then
			S.pv = r.AssemblyLinearVelocity
			S.pa = r.Anchored
			r.Anchored = true
			r.AssemblyLinearVelocity = Vector3.zero
		else
			r.Anchored = S.pa
			r.AssemblyLinearVelocity = S.pv
		end
	end
	setParticles()
	if refreshUI then refreshUI() end
end

local function applyAt(t)
	local cf, v, a, b, k = interpolate(S.frames, t)
	if not cf then return end
	local _, h, r = chr()
	if not r then return end
	local rate = S.scale * (S.mode == "play" and CFG.PlayMuls[S.pmulIdx] or 1)
	if S.rev then rate = -rate end
	r.CFrame = cf
	local scaledVelocity = v * rate
	if S.paused then S.pv = scaledVelocity else r.AssemblyLinearVelocity = scaledVelocity end
	if h then
		h.Jump = a.j == true
		h:Move(a.mv or Vector3.zero, false)
		if a.s ~= S.lastState and a.s ~= 15 then
			S.lastState = a.s
			pcall(function() h:ChangeState(Enum.HumanoidStateType:FromValue(a.s)) end)
		end
	end
end

local function pushFrame(h, r, vreal)
	local fr = {
		t = S.gt,
		cf = r.CFrame,
		v = vreal or r.AssemblyLinearVelocity,
		s = h:GetState().Value,
		mv = h.MoveDirection,
		j = h.Jump,
	}
	if S.cam then
		local c = workspace.CurrentCamera
		if c then fr.cam = c.CFrame; fr.fov = c.FieldOfView end
	end
	S.frames[#S.frames + 1] = fr
end

local function stopAll(keepPlaybackUIHidden)
	local wasPlay = S.mode == "play"
	S.mode = "idle"
	S.stepReq = 0
	if wasPlay then
		S.pv = Vector3.zero
		local _, h = chr()
		if h then h.AutoRotate = S.ar end
		setControls(true)
		if not keepPlaybackUIHidden then
			playbackHideToken += 1
			playbackUiLocked = false
			menuManualVisible = true
			menuForceVisible = false
		end
	end
	restoreCam()
	if S.paused then setPaused(false) end
	if refreshUI then refreshUI() end
end

local function startRecord()
	playbackHideToken += 1
	playbackUiLocked = false
	menuManualVisible = true
	menuForceVisible = false
	local _, h, r = chr()
	if not r then return notify("Нет персонажа") end
	if S.mode ~= "idle" then stopAll() end
	if #S.frames > 0 then
		snapshot()
		S.ghostFrames = copyFrames(S.frames)
	end
	S.frames = {}
	S.legacyFrames = false
	S.gt = 0
	S.mA, S.mB = nil, nil
	S.mode = "record"
	pushFrame(h, r)
	refreshUI()
	notify("Запись пошла")
end

local function startPlay(paused)
	if #S.frames == 0 then return notify("Нет записи") end
	if S.mode == "record" then S.mode = "idle"; S.stepReq = 0 end
	if S.mode ~= "play" then
		if S.paused then setPaused(false) end
		playbackHideToken += 1
		playbackUiLocked = true
		menuForceVisible = false
		S.mode = "play"
		local _, h = chr()
		if h then S.ar = h.AutoRotate; h.AutoRotate = false end
		setControls(false)
		S.gt = S.rev and totalTime() or 0
		S.lastState = nil
	end
	applyAt(S.gt)
	setPaused(paused)
	refreshUI()
end

local function seekTo(frac)
	if #S.frames == 0 or S.mode == "record" then return end
	if S.mode ~= "play" then startPlay(true) end
	S.gt = math.clamp(frac, 0, 1) * totalTime()
	applyAt(S.gt)
end

local function seekTime(t)
	if #S.frames == 0 or S.mode == "record" then return end
	if S.mode ~= "play" then startPlay(true) end
	S.gt = math.clamp(t, 0, totalTime())
	applyAt(S.gt)
end

local function rewindToIndex(i, quiet)
	local f = S.frames
	if S.mode ~= "record" or #f == 0 then return end
	i = math.clamp(i, 1, #f)
	if not quiet then
		snapshot()
		S.ghostFrames = copyFrames(f)
	end
	for k = #f, i + 1, -1 do f[k] = nil end
	local fr = f[i]
	S.gt = fr.t
	S.stepReq = 0
	setPaused(true)
	local _, _, r = chr()
	if r then
		r.CFrame = fr.cf
		S.pv = fr.v * (S.legacyFrames and S.scale or 1)
	end
end

local function rewindSec(sec)
	if S.mode == "play" then
		S.gt = math.max(0, S.gt - sec)
		applyAt(S.gt)
		return
	end
	if S.mode ~= "record" or #S.frames < 2 then return notify("Откат работает в записи") end
	local _, _, _, i = sample(S.frames, S.gt - sec)
	rewindToIndex(i, false)
	notify(("Откат -%gс (на паузе)"):format(sec))
end

local function recordFromHere()
	if S.mode ~= "play" or #S.frames == 0 then return notify("Сначала открой запись (PLAY / перемотка)") end
	snapshot()
	S.ghostFrames = copyFrames(S.frames)
	local _, _, _, i = sample(S.frames, S.gt)
	for k = #S.frames, i + 1, -1 do S.frames[k] = nil end
	S.gt = S.frames[i].t
	if S.legacyFrames then
		local conversionScale = math.max(S.scale, CFG.MinScale)
		for _, fr in ipairs(S.frames) do
			fr.t = fr.t / conversionScale
			fr.v *= conversionScale
		end
		S.gt /= conversionScale
		S.legacyFrames = false
	end
	applyAt(S.gt)
	local _, h = chr()
	setPaused(true)
	playbackHideToken += 1
	playbackUiLocked = false
	menuManualVisible = true
	S.mode = "record"
	S.stepReq = 0
	local _, baseVelocity = interpolate(S.frames, S.gt)
	if baseVelocity then S.pv = baseVelocity * S.scale end
	if h then h.AutoRotate = S.ar end
	setControls(true)
	restoreCam()
	refreshUI()
	notify("REC отсюда: жми ПАУЗА или кадр ▶")
end

local function stepFrame(dir)
	if S.stepReq ~= 0 then return end
	if S.mode == "record" then
		if not S.paused then setPaused(true) end
		if dir > 0 then
			S.stepRemaining = 3
			S.stepReq = 1
		else
			rewindToIndex(#S.frames - 3, true)
		end
		return
	end
	if #S.frames == 0 then return end
	if S.mode ~= "play" then startPlay(true) end
	if not S.paused then setPaused(true) end
	local _, _, _, index = sample(S.frames, S.gt)
	index = math.clamp((index or 1) + dir * 3, 1, #S.frames)
	S.gt = S.frames[index].t
	applyAt(S.gt)
end

local function saveSlot(n)
	local _, h, r = chr()
	if not r then return end
	local v = (S.paused and S.pv or r.AssemblyLinearVelocity) / (S.legacyFrames and S.scale or 1)
	S.slots[n] = { cf = r.CFrame, v = v, t = S.gt, idx = #S.frames, fr = S.frames[#S.frames], st = h:GetState().Value }
	notify("Слот " .. n .. " сохранён")
end

local function loadSlot(n)
	local s = S.slots[n]
	if not s then return notify("Слот " .. n .. " пуст") end
	local _, _, r = chr()
	if not r then return end
	if S.mode == "record" then
		if s.fr and S.frames[s.idx] == s.fr then
			rewindToIndex(s.idx, false)
			notify("Слот " .. n .. " загружен (пауза)")
		else
			notify("Слот из другой ветки записи")
		end
	elseif S.mode == "play" then
		S.gt = s.t
		applyAt(S.gt)
	else
		r.CFrame = s.cf
		r.AssemblyLinearVelocity = s.v * (S.legacyFrames and S.scale or 1)
	end
end

local function guardEdit()
	if S.mode == "record" then notify("Останови запись (⏹ REC)"); return false end
	if #S.frames == 0 then notify("Нет записи"); return false end
	return true
end

local function afterEdit()
	S.gt = math.clamp(S.gt, 0, totalTime())
	if S.mode == "play" then applyAt(S.gt) end
end

local function trimBefore()
	if not guardEdit() then return end
	snapshot()
	local t0, new = S.gt, {}
	for _, fr in ipairs(S.frames) do
		if fr.t >= t0 then new[#new + 1] = shiftFrame(fr, -t0) end
	end
	if #new == 0 then return notify("Пусто") end
	S.frames = new; S.gt = 0; S.mA, S.mB = nil, nil
	afterEdit(); notify("Обрезано до текущего момента")
end

local function trimAfter()
	if not guardEdit() then return end
	snapshot()
	local t0, new = S.gt, {}
	for _, fr in ipairs(S.frames) do
		if fr.t <= t0 then new[#new + 1] = fr end
	end
	if #new == 0 then return notify("Пусто") end
	S.frames = new; S.mA, S.mB = nil, nil
	afterEdit(); notify("Обрезано после текущего момента")
end

local function cutAB()
	if not guardEdit() then return end
	if not (S.mA and S.mB) then return notify("Поставь маркеры A и B") end
	snapshot()
	local t1, t2 = math.min(S.mA, S.mB), math.max(S.mA, S.mB)
	local new = {}
	for _, fr in ipairs(S.frames) do
		if fr.t < t1 then new[#new + 1] = fr
		elseif fr.t > t2 then new[#new + 1] = shiftFrame(fr, -(t2 - t1)) end
	end
	if #new == 0 then return notify("Пусто") end
	S.frames = new; S.mA, S.mB = nil, nil
	S.gt = math.min(S.gt, t1)
	afterEdit(); notify(("Вырезано %.2f c"):format(t2 - t1))
end

local function smoothFrames()
	if not guardEdit() then return end
	local f = S.frames
	if #f < 3 then return end
	snapshot()
	local new = { f[1] }
	for i = 2, #f - 1 do
		local a, b, c = f[i - 1], f[i], f[i + 1]
		local pos = (a.cf.Position + b.cf.Position * 2 + c.cf.Position) / 4
		local n = {}
		for k, v in pairs(b) do n[k] = v end
		n.cf = b.cf.Rotation + pos
		new[#new + 1] = n
	end
	new[#new + 1] = f[#f]
	S.frames = new
	afterEdit(); notify("Сглажено (проверь коллизии)")
end

local function doUndo()
	if #S.undo == 0 then return notify("Undo пуст") end
	if S.mode == "record" then S.mode = "idle"; S.stepReq = 0 end
	S.frames = table.remove(S.undo)
	S.legacyFrames = table.remove(S.undoLegacy) or false
	S.gt = math.clamp(S.gt, 0, totalTime())
	S.mA, S.mB = nil, nil
	if S.mode == "play" then applyAt(S.gt) end
	refreshUI(); notify("Undo")
end

local function clearAll()
	stopAll()
	if #S.frames > 0 then snapshot() end
	S.frames = {}; S.legacyFrames = false; S.gt = 0; S.mA, S.mB = nil, nil
	notify("Запись очищена (Undo вернёт)")
end

local ghost

local function saveBest()
	if #S.frames < 2 then return notify("Нет записи") end
	S.best = copyFrames(S.frames)
	S.bestTime = totalTime()
	notify(("⭐ Лучший забег: %.2f c"):format(S.bestTime))
end

local trailFolder, trailN, trailLast = nil, -1, nil
local function clearTrail()
	if trailFolder then trailFolder:Destroy(); trailFolder = nil end
	trailN, trailLast = -1, nil
end
local function drawTrail()
	clearTrail()
	local f = S.frames
	if #f < 2 then return end
	trailFolder = Instance.new("Folder")
	trailFolder.Name = "TASTrail"
	trailFolder.Parent = workspace
	trailN, trailLast = #f, f[#f]
	local total = totalTime()
	local step = math.max(CFG.TrailStep, total / CFG.TrailMax)
	local function dot(pos, size, color)
		local p = Instance.new("Part")
		p.Shape = Enum.PartType.Ball
		p.Size = Vector3.new(size, size, size)
		p.Anchored = true; p.CanCollide = false; p.CanQuery = false; p.CanTouch = false; p.CastShadow = false
		p.Material = Enum.Material.Neon
		p.Color = color
		p.Position = pos
		p.Parent = trailFolder
	end
	local t = 0
	while t <= total do
		local a, b, k = sample(f, t)
		local cf = (b and k > 0) and a.cf:Lerp(b.cf, k) or a.cf
		local sp = Vector3.new(a.v.X, 0, a.v.Z).Magnitude
		dot(cf.Position, 0.5, Color3.fromHSV(0.62 * (1 - math.clamp(sp / 40, 0, 1)), 0.9, 1))
		t += step
	end
end

local function makeGhost()
	local c = lp.Character
	if not c then return end
	local ok, cl = pcall(function() c.Archivable = true; return c:Clone() end)
	if ok and cl then
		local kill = {}
		for _, d in ipairs(cl:GetDescendants()) do
			if d:IsA("BasePart") then
				d.Anchored = true; d.CanCollide = false; d.CanTouch = false; d.CanQuery = false
				d.Transparency = (d.Name == "HumanoidRootPart") and 1 or 0.7
			elseif d:IsA("LuaSourceContainer") or d:IsA("Sound") or d:IsA("BillboardGui") or d:IsA("ForceField") then
				kill[#kill + 1] = d
			elseif d:IsA("Decal") then
				d.Transparency = 0.7
			end
		end
		for _, d in ipairs(kill) do d:Destroy() end
		local hum = cl:FindFirstChildOfClass("Humanoid")
		if hum then hum.DisplayDistanceType = Enum.HumanoidDisplayDistanceType.None end
		local hl = Instance.new("Highlight")
		hl.FillColor = Color3.fromRGB(90, 170, 255)
		hl.OutlineColor = Color3.fromRGB(160, 215, 255)
		hl.FillTransparency = 0.6
		hl.Parent = cl
		cl.Name = "TASGhost"
		cl.Parent = workspace
		ghost = cl
	else
		local p = Instance.new("Part")
		p.Anchored = true; p.CanCollide = false; p.CanQuery = false; p.CanTouch = false
		p.Size = Vector3.new(2, 5, 1); p.Material = Enum.Material.Neon
		p.Color = Color3.fromRGB(90, 170, 255); p.Transparency = 0.6; p.Name = "TASGhost"
		p.Parent = workspace
		ghost = p
	end
end
local function killGhost()
	if ghost then ghost:Destroy(); ghost = nil end
end

local function r3(x)
	local scaled = x * 1000000
	return (x >= 0 and math.floor(scaled + 0.5) or math.ceil(scaled - 0.5)) / 1000000
end

local function serialize()
	local out = { v = S.legacyFrames and 4 or 5, f = {} }
	for i, fr in ipairs(S.frames) do
		local c = { fr.cf:GetComponents() }
		local row = { r3(fr.t) }
		for j = 1, 12 do row[#row + 1] = r3(c[j]) end
		row[#row + 1] = r3(fr.v.X); row[#row + 1] = r3(fr.v.Y); row[#row + 1] = r3(fr.v.Z)
		row[#row + 1] = fr.s
		local mv = fr.mv or Vector3.zero
		row[#row + 1] = r3(mv.X); row[#row + 1] = r3(mv.Y); row[#row + 1] = r3(mv.Z)
		row[#row + 1] = fr.j and 1 or 0
		if fr.cam then
			local cc = { fr.cam:GetComponents() }
			for j = 1, 12 do row[#row + 1] = r3(cc[j]) end
			row[#row + 1] = r3(fr.fov or 70)
		end
		out.f[i] = row
	end
	return HttpService:JSONEncode(out)
end

local function deserialize(str)
	local ok, data = pcall(function() return HttpService:JSONDecode(str) end)
	if not ok or type(data) ~= "table" or type(data.f) ~= "table" then return false end
	local valid, frames = pcall(function()
		local out = {}
		local lastTime = -math.huge
		for i, r in ipairs(data.f) do
			if type(r) ~= "table" or #r < 17 then error("invalid frame") end
			for j = 1, 17 do
				if type(r[j]) ~= "number" then error("invalid frame value") end
			end
			local t = r[1]
			if t <= lastTime then t = lastTime + 0.000001 end
			lastTime = t
			local fr = {
				t = t,
				cf = CFrame.new(table.unpack(r, 2, 13)),
				v = Vector3.new(r[14], r[15], r[16]),
				s = r[17],
				mv = Vector3.zero,
				j = false,
			}
			if #r >= 21 then
				for j = 18, 21 do
					if type(r[j]) ~= "number" then error("invalid input data") end
				end
				fr.mv = Vector3.new(r[18], r[19], r[20])
				fr.j = r[21] == 1
			end
			if #r >= 34 then
				for j = 22, 34 do
					if type(r[j]) ~= "number" then error("invalid camera data") end
				end
				fr.cam = CFrame.new(table.unpack(r, 22, 33))
				fr.fov = r[34]
			end
			out[i] = fr
		end
		return out
	end)
	if not valid or #frames == 0 then return false end
	if S.mode ~= "idle" then stopAll() end
	if #S.frames > 0 then snapshot() end
	S.frames = frames
	S.legacyFrames = (tonumber(data.v) or 4) < 5
	S.gt = 0
	S.mA, S.mB = nil, nil
	return true
end

local PLAYER_SRC = [==[
local RunService = game:GetService("RunService")
local HttpService = game:GetService("HttpService")
local lp = game:GetService("Players").LocalPlayer
local raw = HttpService:JSONDecode(data)
local frames = {}
for i, r in ipairs(raw.f) do
	frames[i] = {
		t = r[1],
		cf = CFrame.new(table.unpack(r, 2, 13)),
		v = Vector3.new(r[14], r[15], r[16]),
		s = r[17],
		mv = (#r >= 20) and Vector3.new(r[18], r[19], r[20]) or Vector3.zero,
		j = (#r >= 21) and r[21] == 1 or false,
		cam = (#r >= 34) and CFrame.new(table.unpack(r, 22, 33)) or nil,
		fov = (#r >= 34) and r[34] or nil,
	}
end
local function sample(t)
	local lo, hi = 1, #frames
	while lo < hi do
		local mid = (lo + hi + 1) // 2
		if frames[mid].t <= t then lo = mid else hi = mid - 1 end
	end
	local a, b = frames[lo], frames[lo + 1]
	local k = 0
	if b and b.t > a.t then k = math.clamp((t - a.t) / (b.t - a.t), 0, 1) end
	return a, b, k
end
local function interpolate(t)
	local a, b, k = sample(t)
	if not b or k <= 0 then return a.cf, a.v, a, b, k end
	local span = math.max(b.t - a.t, 1e-5)
	local p0, p1 = a.cf.Position, b.cf.Position
	local delta = p1 - p0
	local m0, m1 = a.v * span, b.v * span
	local chordLength = delta.Magnitude
	if chordLength < 1e-4 then
		m0, m1 = Vector3.zero, Vector3.zero
	else
		local direction = delta / chordLength
		local along0, along1 = m0:Dot(direction), m1:Dot(direction)
		if along0 < 0 then m0 -= direction * along0 end
		if along1 < 0 then m1 -= direction * along1 end
		local maxTangent = chordLength * 3
		if m0.Magnitude > maxTangent then m0 = m0.Unit * maxTangent end
		if m1.Magnitude > maxTangent then m1 = m1.Unit * maxTangent end
		local alpha, beta = m0:Dot(direction) / chordLength, m1:Dot(direction) / chordLength
		local tangentSum = alpha * alpha + beta * beta
		if tangentSum > 9 then
			local limiter = 3 / math.sqrt(tangentSum)
			m0 *= limiter
			m1 *= limiter
		end
	end
	local k2, k3 = k * k, k * k * k
	local pos = p0 * (2 * k3 - 3 * k2 + 1) + m0 * (k3 - 2 * k2 + k) + p1 * (-2 * k3 + 3 * k2) + m1 * (k3 - k2)
	local vel = (p0 * (6 * k2 - 6 * k) + m0 * (3 * k2 - 4 * k + 1) + p1 * (-6 * k2 + 6 * k) + m1 * (3 * k2 - 2 * k)) / span
	return CFrame.new(pos) * a.cf:Lerp(b.cf, k).Rotation, vel, a, b, k
end
local char = lp.Character or lp.CharacterAdded:Wait()
local hum = char:WaitForChild("Humanoid")
local root = char:WaitForChild("HumanoidRootPart")
local cam = workspace.CurrentCamera
local controls = require(lp.PlayerScripts:WaitForChild("PlayerModule")):GetControls()
local prevAR, prevCam, prevFov = hum.AutoRotate, cam.CameraType, cam.FieldOfView
controls:Disable()
hum.AutoRotate = false
local lastState
local t, total = 0, frames[#frames].t
local conn
conn = RunService.PreSimulation:Connect(function(dt)
	t = math.min(t + dt, total)
	local cf, vel, a, b, k = interpolate(t)
	root.CFrame = cf
	root.AssemblyLinearVelocity = vel
	hum.Jump = a.j == true
	hum:Move(a.mv or Vector3.zero, false)
	if a.s and a.s ~= lastState and a.s ~= 15 then
		lastState = a.s
		pcall(function() hum:ChangeState(Enum.HumanoidStateType:FromValue(a.s)) end)
	end
	if a.cam then
		cam.CameraType = Enum.CameraType.Scriptable
		cam.CFrame = (b and b.cam) and a.cam:Lerp(b.cam, k) or a.cam
		if a.fov then cam.FieldOfView = b and b.fov and (a.fov + (b.fov - a.fov) * k) or a.fov end
	end
	if t >= total then
		conn:Disconnect()
		hum.AutoRotate = prevAR
		cam.CameraType = prevCam
		cam.FieldOfView = prevFov
		controls:Enable()
	end
end)
]==]

local function exportLua()
	return "local data = [===[" .. serialize() .. "]===]\n" .. PLAYER_SRC
end

local SAVE_INDEX = "cocosTAS_saves.json"
local SAVE_AUTO = "cocosTAS_autosave.json"
local saveCatalog = {}
local selectedSaveId = nil

local function fileApiReady()
	return type(writefile) == "function" and type(readfile) == "function"
end

local function readFileSafe(path)
	if not fileApiReady() then return nil end
	local ok, data = pcall(readfile, path)
	return ok and type(data) == "string" and data or nil
end

local function writeFileSafe(path, data)
	if type(writefile) ~= "function" then return false end
	local ok = pcall(writefile, path, data)
	return ok
end

local function persistCatalog()
	if not fileApiReady() then return false end
	local ok, encoded = pcall(function()
		return HttpService:JSONEncode({ version = 1, saves = saveCatalog })
	end)
	return ok and writeFileSafe(SAVE_INDEX, encoded) or false
end

local function loadSaveCatalog()
	saveCatalog = {}
	local raw = readFileSafe(SAVE_INDEX)
	if not raw then return false end
	local ok, data = pcall(function() return HttpService:JSONDecode(raw) end)
	if not ok or type(data) ~= "table" or type(data.saves) ~= "table" then return false end
	for _, item in ipairs(data.saves) do
		if type(item) == "table" and type(item.id) == "string" and type(item.name) == "string" then
			saveCatalog[#saveCatalog + 1] = {
				id = item.id,
				name = item.name,
				created = tonumber(item.created) or 0,
				frames = tonumber(item.frames) or 0,
				duration = tonumber(item.duration) or 0,
			}
		end
	end
	table.sort(saveCatalog, function(a, b) return a.created > b.created end)
	return true
end

local function saveFilePath(id)
	return "cocosTAS_save_" .. id .. ".json"
end

local function autosave()
	if #S.frames < 2 or not fileApiReady() then return false end
	return writeFileSafe(SAVE_AUTO, serialize())
end

local function loadAutosave()
	local raw = readFileSafe(SAVE_AUTO)
	return raw and deserialize(raw) or false
end

local function cleanSaveName(value)
	value = tostring(value or "")
	value = value:gsub("^%s+", ""):gsub("%s+$", "")
	local ok, offset = pcall(function() return utf8.offset(value, 49) end)
	if ok and offset then value = value:sub(1, offset - 1) end
	return value
end

local function saveNamedRecording(name)
	name = cleanSaveName(name)
	if name == "" then return notify("Введи название записи") end
	if #S.frames < 2 then return notify("Сначала сделай запись") end
	if not fileApiReady() then return notify("Файловое сохранение недоступно в этой среде") end
	local id = tostring(os.time()) .. "_" .. HttpService:GenerateGUID(false):gsub("[^%w]", "")
	local payload = serialize()
	if not writeFileSafe(saveFilePath(id), payload) then return notify("Не удалось сохранить файл записи") end
	table.insert(saveCatalog, 1, {
		id = id,
		name = name,
		created = os.time(),
		frames = #S.frames,
		duration = totalTime(),
	})
	if not persistCatalog() then
		table.remove(saveCatalog, 1)
		return notify("Запись сохранена, но каталог не удалось обновить")
	end
	selectedSaveId = id
	if refreshSaveList then refreshSaveList() end
	notify("Сохранено: " .. name)
end

local function findSelectedSave()
	for i, item in ipairs(saveCatalog) do
		if item.id == selectedSaveId then return item, i end
	end
end

local function loadSelectedSave()
	local item = findSelectedSave()
	if not item then return notify("Выбери запись в списке") end
	local raw = readFileSafe(saveFilePath(item.id))
	if not raw or not deserialize(raw) then return notify("Файл записи не найден или повреждён") end
	notify("Загружено: " .. item.name)
end

local function renameSelectedSave(name)
	local item = findSelectedSave()
	if not item then return notify("Выбери запись в списке") end
	name = cleanSaveName(name)
	if name == "" then return notify("Введи новое название") end
	item.name = name
	if not persistCatalog() then return notify("Не удалось обновить каталог") end
	if refreshSaveList then refreshSaveList() end
	notify("Название изменено")
end

local function deleteSelectedSave()
	local item, index = findSelectedSave()
	if not item then return notify("Выбери запись в списке") end
	if type(delfile) == "function" then pcall(delfile, saveFilePath(item.id)) end
	table.remove(saveCatalog, index)
	selectedSaveId = nil
	if not persistCatalog() then return notify("Не удалось обновить каталог") end
	if refreshSaveList then refreshSaveList() end
	notify("Запись удалена из списка")
end

local host = (gethui and gethui()) or lp:WaitForChild("PlayerGui")
local old = host:FindFirstChild("cocosTAS")
if old then old:Destroy() end

local function mk(class, props, parent)
	local o = Instance.new(class)
	for k, v in pairs(props) do o[k] = v end
	o.Parent = parent
	return o
end

local C = {
	bg = Color3.fromRGB(18, 21, 29),
	bar = Color3.fromRGB(29, 35, 48),
	btn = Color3.fromRGB(42, 50, 67),
	on = Color3.fromRGB(74, 137, 230),
	rec = Color3.fromRGB(207, 73, 87),
	ok = Color3.fromRGB(79, 177, 133),
	text = Color3.fromRGB(239, 243, 250),
	dim = Color3.fromRGB(157, 168, 188),
}

local function isPress(i)
	return i.UserInputType == Enum.UserInputType.Touch or i.UserInputType == Enum.UserInputType.MouseButton1
end
local function isMove(i)
	return i.UserInputType == Enum.UserInputType.Touch or i.UserInputType == Enum.UserInputType.MouseMovement
end

local gui = mk("ScreenGui", {
	Name = "cocosTAS", ResetOnSpawn = false, IgnoreGuiInset = true,
	ZIndexBehavior = Enum.ZIndexBehavior.Sibling, DisplayOrder = 999,
}, host)

local WIDTH, HEIGHT = 252, 252
local main = mk("Frame", {
	Size = UDim2.fromOffset(WIDTH, HEIGHT), Position = UDim2.new(0, 10, 0, 10),
	BackgroundColor3 = C.bg, BorderSizePixel = 0, Active = true,
}, gui)
mk("UICorner", { CornerRadius = UDim.new(0, 10) }, main)
mk("UIStroke", { Color = Color3.fromRGB(75, 91, 119), Thickness = 1.2, Transparency = 0.25 }, main)
local uiScale = mk("UIScale", {}, main)
local function fitScale()
	local cam = workspace.CurrentCamera
	local vp = cam and cam.ViewportSize or Vector2.new(800, 600)
	uiScale.Scale = math.clamp(math.min(vp.Y / 520, vp.X / 300), 0.68, 1)
end
fitScale()
conns[#conns + 1] = workspace:GetPropertyChangedSignal("CurrentCamera"):Connect(fitScale)

local title = mk("Frame", { Size = UDim2.new(1, 0, 0, 26), BackgroundColor3 = C.bar, BorderSizePixel = 0 }, main)
mk("UICorner", { CornerRadius = UDim.new(0, 10) }, title)
mk("UIGradient", { Color = ColorSequence.new(Color3.fromRGB(39, 49, 68), Color3.fromRGB(27, 32, 44)), Rotation = 0 }, title)
mk("TextLabel", {
	Text = "  cocosTAS", Size = UDim2.new(1, -70, 1, 0), BackgroundTransparency = 1,
	TextColor3 = C.text, Font = Enum.Font.GothamBold, TextSize = 13, TextXAlignment = Enum.TextXAlignment.Left,
}, title)

local body = mk("Frame", { Size = UDim2.new(1, 0, 1, -26), Position = UDim2.fromOffset(0, 26), BackgroundTransparency = 1, ClipsDescendants = true }, main)

local function btn(par, txt, x, y, w, h, col, cb, size)
	local b = mk("TextButton", {
		Text = txt, Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(w, h),
		BackgroundColor3 = col or C.btn, TextColor3 = C.text, Font = Enum.Font.GothamMedium,
		TextSize = size or 11, BorderSizePixel = 0, AutoButtonColor = true, TextWrapped = true,
	}, par)
	mk("UICorner", { CornerRadius = UDim.new(0, 7) }, b)
	b.Activated:Connect(cb)
	return b
end

local minimized = false
local wallhopEnabled = false
local wallhopNext = 0
local wallhopCooldown = 0.24
local wallhopLostAt = 0
local wallhopArmed = true
local wallhopPush = 11
local wallhopMaxHorizontal = 42

local function wallhopStep()
	if not wallhopEnabled or S.mode == "play" or S.paused then return end
	local character, humanoid, root = chr()
	if not character or not humanoid or not root or humanoid.Health <= 0 then return end
	if humanoid.FloorMaterial ~= Enum.Material.Air then
		wallhopArmed = true
		wallhopLostAt = 0
		return
	end
	local state = humanoid:GetState()
	if state ~= Enum.HumanoidStateType.Freefall and state ~= Enum.HumanoidStateType.Jumping then return end

	local move = humanoid.MoveDirection
	local look = Vector3.new(root.CFrame.LookVector.X, 0, root.CFrame.LookVector.Z)
	local forward = move.Magnitude > 0.12 and move.Unit or (look.Magnitude > 0.01 and look.Unit or Vector3.new(0, 0, -1))
	local right = Vector3.new(-forward.Z, 0, forward.X)
	local directions = {
		forward, right, -right, -forward,
		(forward + right).Unit, (forward - right).Unit,
		(-forward + right).Unit, (-forward - right).Unit,
	}
	local params = RaycastParams.new()
	params.FilterType = Enum.RaycastFilterType.Exclude
	params.FilterDescendantsInstances = { character }
	params.IgnoreWater = true

	local nearest
	local heights = { 0.15, 0.95, 1.75 }
	for _, height in ipairs(heights) do
		local origin = root.Position + Vector3.new(0, height, 0)
		for _, direction in ipairs(directions) do
			local hit = workspace:Raycast(origin, direction * 2.9, params)
			if hit and hit.Instance and hit.Instance.CanCollide and math.abs(hit.Normal.Y) < 0.25 then
				if not nearest or hit.Distance < nearest.Distance then
					nearest = hit
				end
			end
		end
	end

	local now = os.clock()
	if not nearest then
		if wallhopLostAt == 0 then wallhopLostAt = now end
		if now - wallhopLostAt >= 0.12 then wallhopArmed = true end
		return
	end

	wallhopLostAt = 0
	if not wallhopArmed or now < wallhopNext then return end

	local away = Vector3.new(nearest.Normal.X, 0, nearest.Normal.Z)
	if away.Magnitude < 0.1 then return end
	away = away.Unit

	local velocity = root.AssemblyLinearVelocity
	local horizontal = Vector3.new(velocity.X, 0, velocity.Z)
	local intoWall = horizontal:Dot(away)
	if intoWall < 0 then
		horizontal -= away * intoWall
	end
	horizontal += away * wallhopPush
	if horizontal.Magnitude > wallhopMaxHorizontal then
		horizontal = horizontal.Unit * wallhopMaxHorizontal
	end

	root.AssemblyLinearVelocity = Vector3.new(
		horizontal.X,
		velocity.Y,
		horizontal.Z
	)

	wallhopArmed = false
	wallhopNext = now + wallhopCooldown
end
local minimizeBtn = btn(title, "−", 198, 1, 22, 23, C.btn, function() end, 13)
local activeTweens = {}
local tweenInfo = TweenInfo.new(0.22, Enum.EasingStyle.Quint, Enum.EasingDirection.Out)
local function animateMinimize(nextValue)
	if minimized == nextValue then return end
	minimized = nextValue
	for _, tw in ipairs(activeTweens) do tw:Cancel() end
	table.clear(activeTweens)
	if minimized then
		minimizeBtn.Text = "+"
		body.Visible = true
		activeTweens[1] = TweenService:Create(main, tweenInfo, { Size = UDim2.fromOffset(WIDTH, 26) })
		activeTweens[2] = TweenService:Create(body, tweenInfo, { Size = UDim2.new(1, 0, 0, 0) })
		activeTweens[1].Completed:Connect(function(state)
			if state == Enum.PlaybackState.Completed and minimized then body.Visible = false end
		end)
	else
		minimizeBtn.Text = "−"
		body.Visible = true
		body.Size = UDim2.new(1, 0, 0, 0)
		activeTweens[1] = TweenService:Create(main, tweenInfo, { Size = UDim2.fromOffset(WIDTH, HEIGHT) })
		activeTweens[2] = TweenService:Create(body, tweenInfo, { Size = UDim2.new(1, 0, 1, -26) })
	end
	for _, tw in ipairs(activeTweens) do tw:Play() end
end
minimizeBtn.Activated:Connect(function() animateMinimize(not minimized) end)

local savePanelOpen = false
local floatControlsEnabled = true
local reopenButton
local W = {}
local mainClose = btn(title, "×", 224, 1, 24, 23, C.rec, function()
	menuManualVisible = false
	menuForceVisible = false
	savePanelOpen = false
	if refreshUI then refreshUI() else
		main.Visible = false
		if reopenButton then reopenButton.Visible = true end
	end
end, 14)

local status = mk("TextLabel", {
	Position = UDim2.fromOffset(7, 3), Size = UDim2.fromOffset(238, 21), BackgroundTransparency = 1,
	TextColor3 = C.dim, Font = Enum.Font.Gotham, TextSize = 10, TextXAlignment = Enum.TextXAlignment.Left,
	TextYAlignment = Enum.TextYAlignment.Center, Text = "Ожидание записи",
}, body)

local prog = mk("Frame", { Position = UDim2.fromOffset(7, 27), Size = UDim2.fromOffset(238, 14), BackgroundTransparency = 1, Active = true }, body)
local progLine = mk("Frame", { Position = UDim2.fromOffset(0, 4), Size = UDim2.new(1, 0, 0, 6), BackgroundColor3 = C.bar, BorderSizePixel = 0 }, prog)
mk("UICorner", { CornerRadius = UDim.new(1, 0) }, progLine)
local progFill = mk("Frame", { Size = UDim2.fromScale(0, 1), BackgroundColor3 = C.on, BorderSizePixel = 0 }, progLine)
mk("UICorner", { CornerRadius = UDim.new(1, 0) }, progFill)

local seeking = false
local function seekFromX(x)
	if prog.AbsoluteSize.X <= 0 then return end
	seekTo(math.clamp((x - prog.AbsolutePosition.X) / prog.AbsoluteSize.X, 0, 1))
end
prog.InputBegan:Connect(function(input)
	if isPress(input) then seeking = true; seekFromX(input.Position.X) end
end)
conns[#conns + 1] = UIS.InputChanged:Connect(function(input)
	if seeking and isMove(input) then seekFromX(input.Position.X) end
end)
conns[#conns + 1] = UIS.InputEnded:Connect(function(input)
	if isPress(input) then seeking = false end
end)

local function toggleRec()
	if S.mode == "record" then
		S.mode = "idle"
		S.stepReq = 0
		if S.paused then setPaused(false) end
		refreshUI()
		autosave()
		notify(("Запись завершена: %d кадров, %.2f с"):format(#S.frames, totalTime()))
	else
		startRecord()
	end
end
local function togglePlay()
	if S.mode == "play" and S.paused then
		setPaused(false)
	else
		if S.mode == "play" then S.gt = S.rev and totalTime() or 0 end
		startPlay(false)
	end
	refreshUI()
end
local function togglePause()
	if S.mode == "idle" then return notify("Сначала начни запись или воспроизведение") end
	setPaused(not S.paused)
end

W.rec = btn(body, "⏺ REC", 7, 47, 75, 32, C.rec, toggleRec, 12)
W.play = btn(body, "▶ PLAY", 88, 47, 75, 32, C.btn, togglePlay, 12)
W.stop = btn(body, "■ STOP", 169, 47, 75, 32, C.btn, function()
	stopAll()
	autosave()
	notify("Остановлено")
end, 12)

W.slowLbl = mk("TextLabel", {
	Position = UDim2.fromOffset(7, 83), Size = UDim2.fromOffset(238, 14), BackgroundTransparency = 1,
	TextColor3 = C.text, Font = Enum.Font.GothamBold, TextSize = 10, TextXAlignment = Enum.TextXAlignment.Left,
	Text = "Скорость времени: x1.00",
}, body)
W.presets = {}
for i, pv in ipairs(CFG.Presets) do
	W.presets[i] = btn(body, pv == 1 and "1x" or ("x" .. tostring(pv)), 7 + (i - 1) * 48, 100, 44, 25, C.btn, function() S.scaleSet(pv) end, 10)
end
W.cam = btn(body, "Камера: ВКЛ", 7, 133, 75, 28, C.on, function()
	S.cam = not S.cam
	if not S.cam then restoreCam() end
	refreshUI()
end, 9)
W.saves = btn(body, "Сохранения", 88, 133, 75, 28, C.btn, function()
	savePanelOpen = not savePanelOpen
	if savePanelOpen then
		refreshSaveList()
		if not fileApiReady() then notify("Для сохранений нужны файловые функции среды") end
	end
	refreshUI()
end, 9)
W.float = btn(body, "Пульт: ВКЛ", 169, 133, 75, 28, C.btn, function()
	floatControlsEnabled = not floatControlsEnabled
	refreshUI()
end, 9)

W.wallhop = btn(body, "Wallhop helper: ВЫКЛ", 7, 166, 238, 27, C.btn, function()
	wallhopEnabled = not wallhopEnabled
	wallhopNext = 0
	refreshUI()
	notify(wallhopEnabled and "Wallhop helper включён" or "Wallhop helper выключен")
end, 10)

local msg = mk("TextLabel", {
	Position = UDim2.fromOffset(7, 198), Size = UDim2.fromOffset(238, 25), TextWrapped = true,
	TextYAlignment = Enum.TextYAlignment.Top, BackgroundTransparency = 1,
	TextColor3 = C.ok, Font = Enum.Font.Gotham, TextSize = 10,
	TextXAlignment = Enum.TextXAlignment.Left, Text = "Нажми REC, чтобы начать запись",
}, body)
local toastUntil = 0
notify = function(t)
	msg.Text = tostring(t)
	toastUntil = os.clock() + 3.5
	msg.TextColor3 = C.ok
end

local savePanel = mk("Frame", {
	Size = UDim2.fromOffset(252, 260), Position = UDim2.new(0, 10, 0, 240),
	BackgroundColor3 = C.bg, BorderSizePixel = 0, Visible = false, Active = true,
}, gui)
mk("UICorner", { CornerRadius = UDim.new(0, 10) }, savePanel)
mk("UIStroke", { Color = Color3.fromRGB(75, 91, 119), Thickness = 1.2, Transparency = 0.25 }, savePanel)
local saveHead = mk("Frame", { Size = UDim2.new(1, 0, 0, 28), BackgroundColor3 = C.bar, BorderSizePixel = 0 }, savePanel)
mk("UICorner", { CornerRadius = UDim.new(0, 10) }, saveHead)
mk("TextLabel", {
	Text = "  МОИ ЗАПИСИ", Size = UDim2.new(1, -35, 1, 0), BackgroundTransparency = 1,
	TextColor3 = C.text, Font = Enum.Font.GothamBold, TextSize = 11, TextXAlignment = Enum.TextXAlignment.Left,
}, saveHead)
btn(saveHead, "×", 222, 2, 24, 24, C.rec, function() savePanelOpen = false; refreshUI() end, 14)

local saveNameBox = mk("TextBox", {
	Position = UDim2.fromOffset(7, 36), Size = UDim2.fromOffset(164, 29),
	BackgroundColor3 = C.bar, TextColor3 = C.text, PlaceholderColor3 = C.dim,
	Font = Enum.Font.Gotham, TextSize = 11, TextXAlignment = Enum.TextXAlignment.Left,
	ClearTextOnFocus = false, Text = "", PlaceholderText = "Название записи", BorderSizePixel = 0,
}, savePanel)
mk("UICorner", { CornerRadius = UDim.new(0, 6) }, saveNameBox)
btn(savePanel, "СОХРАНИТЬ", 176, 36, 69, 29, C.ok, function() saveNamedRecording(saveNameBox.Text) end, 9)

local saveList = mk("ScrollingFrame", {
	Position = UDim2.fromOffset(7, 72), Size = UDim2.fromOffset(238, 126),
	BackgroundColor3 = C.bar, BorderSizePixel = 0, ScrollBarThickness = 4,
	AutomaticCanvasSize = Enum.AutomaticSize.Y, CanvasSize = UDim2.new(),
}, savePanel)
mk("UICorner", { CornerRadius = UDim.new(0, 6) }, saveList)
mk("UIListLayout", { Padding = UDim.new(0, 3), SortOrder = Enum.SortOrder.LayoutOrder }, saveList)

refreshSaveList = function()
	for _, child in ipairs(saveList:GetChildren()) do
		if child:IsA("GuiObject") and not child:IsA("UIListLayout") then child:Destroy() end
	end
	for i, item in ipairs(saveCatalog) do
		local selected = item.id == selectedSaveId
		local label = (item.name .. "   ·   " .. tostring(item.frames) .. " кадров   ·   " .. string.format("%.1fс", item.duration))
		local row = mk("TextButton", {
			Size = UDim2.new(1, -6, 0, 25), Text = label,
			BackgroundColor3 = selected and C.on or C.btn, TextColor3 = C.text,
			Font = Enum.Font.GothamMedium, TextSize = 10, TextXAlignment = Enum.TextXAlignment.Left,
			BorderSizePixel = 0, LayoutOrder = i, AutoButtonColor = true,
		}, saveList)
		mk("UICorner", { CornerRadius = UDim.new(0, 5) }, row)
		row.Activated:Connect(function()
			selectedSaveId = item.id
			saveNameBox.Text = item.name
			refreshSaveList()
		end)
	end
	if #saveCatalog == 0 then
		local empty = mk("TextLabel", {
			Size = UDim2.new(1, -8, 0, 38), BackgroundTransparency = 1,
			Text = "Пока нет сохранений.\nВведи имя и нажми СОХРАНИТЬ.",
			TextColor3 = C.dim, Font = Enum.Font.Gotham, TextSize = 10,
			TextWrapped = true, LayoutOrder = 1,
		}, saveList)
	end
end

btn(savePanel, "ЗАГРУЗИТЬ", 7, 204, 75, 27, C.on, loadSelectedSave, 9)
btn(savePanel, "ПЕРЕИМЕНОВАТЬ", 88, 204, 75, 27, C.btn, function() renameSelectedSave(saveNameBox.Text) end, 8)
btn(savePanel, "УДАЛИТЬ", 169, 204, 76, 27, C.rec, deleteSelectedSave, 9)
btn(savePanel, "Восстановить автосейв", 7, 235, 238, 19, C.btn, function()
	if loadAutosave() then notify("Автосохранение восстановлено") else notify("Автосохранения нет") end
end, 9)

local floatPanel = mk("Frame", {
	Size = UDim2.fromOffset(262, 40), Position = UDim2.new(0.5, -131, 0.82, 0),
	BackgroundColor3 = C.bg, BorderSizePixel = 0, Active = true,
}, gui)
mk("UICorner", { CornerRadius = UDim.new(0, 9) }, floatPanel)
mk("UIStroke", { Color = Color3.fromRGB(75, 91, 119), Thickness = 1.1, Transparency = 0.2 }, floatPanel)
local dragGrip = mk("TextButton", {
	Position = UDim2.fromOffset(2, 4), Size = UDim2.fromOffset(19, 32),
	Text = "⠿", BackgroundColor3 = C.bar, TextColor3 = C.dim,
	Font = Enum.Font.GothamBold, TextSize = 16, BorderSizePixel = 0,
}, floatPanel)
mk("UICorner", { CornerRadius = UDim.new(0, 6) }, dragGrip)
btn(floatPanel, "−0.2с", 24, 5, 35, 30, C.btn, function() rewindSec(0.2) end, 9)
btn(floatPanel, "−0.4с", 61, 5, 35, 30, C.btn, function() rewindSec(0.4) end, 9)
W.floatPause = btn(floatPanel, "Ⅱ", 98, 5, 35, 30, C.on, togglePause, 12)
W.floatStop = btn(floatPanel, "■", 135, 5, 35, 30, C.rec, function()
	if S.mode == "play" then
		finishPlayback()
	else
		stopAll()
	end
end, 12)
btn(floatPanel, "◀", 172, 5, 35, 30, C.btn, function() stepFrame(-1) end, 12)
btn(floatPanel, "▶", 209, 5, 35, 30, C.btn, function() stepFrame(1) end, 12)
btn(floatPanel, "×", 246, 5, 14, 30, C.rec, function() floatControlsEnabled = false; refreshUI() end, 12)

do
	local dragging = false
	local startInput, startPosition
	dragGrip.InputBegan:Connect(function(input)
		if isPress(input) then
			dragging = true
			startInput = input.Position
			startPosition = UDim2.fromOffset(floatPanel.AbsolutePosition.X, floatPanel.AbsolutePosition.Y)
		end
	end)
	conns[#conns + 1] = UIS.InputChanged:Connect(function(input)
		if dragging and isMove(input) then
			local delta = input.Position - startInput
			local cam = workspace.CurrentCamera
			local vp = cam and cam.ViewportSize or Vector2.new(800, 600)
			local x = math.clamp(startPosition.X.Offset + delta.X, 0, math.max(0, vp.X - floatPanel.AbsoluteSize.X))
			local y = math.clamp(startPosition.Y.Offset + delta.Y, 0, math.max(0, vp.Y - floatPanel.AbsoluteSize.Y))
			floatPanel.Position = UDim2.fromOffset(x, y)
		end
	end)
	conns[#conns + 1] = UIS.InputEnded:Connect(function(input)
		if isPress(input) then dragging = false end
	end)
end

local function placeSavePanel()
	local cam = workspace.CurrentCamera
	local vp = cam and cam.ViewportSize or Vector2.new(800, 600)
	local panelW, panelH = 252, 260
	local x = main.AbsolutePosition.X
	local y = main.AbsolutePosition.Y + main.AbsoluteSize.Y + 7
	if x + panelW > vp.X then x = math.max(4, vp.X - panelW - 4) end
	if y + panelH > vp.Y then y = math.max(4, main.AbsolutePosition.Y - panelH - 7) end
	savePanel.Position = UDim2.fromOffset(x, y)
end

reopenButton = btn(gui, "TAS", 10, 10, 44, 30, C.on, function()
	menuManualVisible = true
	menuForceVisible = true
	refreshUI()
end, 11)
reopenButton.Visible = false

local function syncUiVisibility()
	gui.Enabled = true
	local playing = S.mode == "play" or playbackUiLocked
	main.Visible = menuManualVisible and (not playing or menuForceVisible)
	savePanel.Visible = main.Visible and savePanelOpen
	floatPanel.Visible = floatControlsEnabled
	if reopenButton then reopenButton.Visible = not main.Visible end
end

local titleDragging, titleStart, titleOrigin = false, nil, nil
title.InputBegan:Connect(function(input)
	if isPress(input) then
		titleDragging = true
		titleStart = input.Position
		titleOrigin = main.Position
	end
end)
conns[#conns + 1] = UIS.InputChanged:Connect(function(input)
	if titleDragging and isMove(input) then
		local delta = input.Position - titleStart
		local cam = workspace.CurrentCamera
		local vp = cam and cam.ViewportSize or Vector2.new(800, 600)
		local x = math.clamp(titleOrigin.X.Offset + delta.X, 0, math.max(0, vp.X - main.AbsoluteSize.X))
		local y = math.clamp(titleOrigin.Y.Offset + delta.Y, 0, math.max(0, vp.Y - 28))
		main.Position = UDim2.fromOffset(x, y)
		if savePanelOpen then placeSavePanel() end
	end
end)
conns[#conns + 1] = UIS.InputEnded:Connect(function(input)
	if isPress(input) then titleDragging = false end
end)

local function shutdown()
	stopAll()
	S.scale = 1
	S.paused = false
	applySlow()
	killGhost()
	restoreCam()
	setControls(true)
	pcall(function() RunService:UnbindFromRenderStep("cocosTASCamera") end)
	for _, c in ipairs(conns) do c:Disconnect() end
	clearTrail()
	gui:Destroy()
end

local logMin = math.log10(CFG.MinScale)
local function curMul() return CFG.PlayMuls[S.pmulIdx] end

function S.scaleSet(v)
	v = math.clamp(v, CFG.MinScale, 1)
	if v > 0.97 then v = 1 end
	local old = S.scale
	S.scale = v
	local _, _, r = chr()
	if old > 0 and S.mode ~= "play" then
		if S.paused then
			S.pv = S.pv * (v / old)
		elseif r then
			r.AssemblyLinearVelocity = r.AssemblyLinearVelocity * (v / old)
		end
	end
	refreshUI()
	setParticles()
end

refreshUI = function()
	W.rec.Text = S.mode == "record" and "■ СТОП REC" or "⏺ ЗАПИСЬ"
	W.rec.BackgroundColor3 = S.mode == "record" and C.rec or C.btn
	W.play.Text = (S.mode == "play" and S.paused) and "▶ ПРОДОЛЖИТЬ" or "▶ PLAY"
	W.play.BackgroundColor3 = (S.mode == "play" and not S.paused) and C.on or C.btn
	W.stop.BackgroundColor3 = C.btn
	local p = 1 - math.log10(S.scale) / logMin
	W.slowLbl.Text = ("Скорость времени: x%.2f"):format(S.scale)
	for i, pv in ipairs(CFG.Presets) do
		W.presets[i].BackgroundColor3 = math.abs(S.scale - pv) < 0.001 and C.on or C.btn
	end
	W.cam.Text = S.cam and "Камера: ВКЛ" or "Камера: ВЫКЛ"
	W.cam.BackgroundColor3 = S.cam and C.on or C.btn
	W.saves.BackgroundColor3 = savePanelOpen and C.on or C.btn
	W.float.Text = floatControlsEnabled and "Пульт: ВКЛ" or "Пульт: ВЫКЛ"
	W.float.BackgroundColor3 = floatControlsEnabled and C.on or C.btn
	W.floatPause.Text = S.paused and "▶" or "Ⅱ"
	W.floatPause.BackgroundColor3 = S.paused and C.on or C.btn
	W.wallhop.Text = wallhopEnabled and "Wallhop helper: ВКЛ" or "Wallhop helper: ВЫКЛ"
	W.wallhop.BackgroundColor3 = wallhopEnabled and C.on or C.btn
	progFill.Size = UDim2.fromScale(totalTime() > 0 and math.clamp(S.gt / totalTime(), 0, 1) or 0, 1)
	syncUiVisibility()
	if savePanelOpen then placeSavePanel() end
end

finishPlayback = function()
	if S.mode ~= "play" then return end
	stopAll(true)
	notify("Воспроизведение завершено")
	local token = playbackHideToken
	task.delay(5, function()
		if token == playbackHideToken and S.mode ~= "play" then
			playbackUiLocked = false
			menuManualVisible = true
			menuForceVisible = false
			if refreshUI then refreshUI() end
		end
	end)
end

local function hint()
	if S.mode == "record" then
		if S.paused then return "⏸ Пауза. Жми «кадр ▶» (по 3 кадра) или ⏸ ещё раз, чтобы продолжить запись." end
		return "Идёт запись. Для повтора используй откат или покадровый шаг."
	elseif S.mode == "play" then
		if S.paused then return "Пауза. Тапни по полосе выше для перемотки или нажми кадр для точного шага. TAS / F1 — меню." end
		return "Воспроизведение. TAS / F1 — вернуть меню."
	end
	if #S.frames == 0 then return "Нажми ⏺ и пройди свою трассу. TAS / F1 — вернуть меню." end
	return "Запись готова: ▶ просмотр или СОХРАНЕНИЯ. TAS / F1 — меню."
end

local acc, partAcc, autoAcc = 0, 0, 0
conns[#conns + 1] = RunService.PreSimulation:Connect(function(dt)
	applySlow()
	wallhopStep()

	if S.stepReq == 1 then
		local _, _, r = chr()
		if r and S.mode == "record" then
			r.Anchored = S.pa
			r.AssemblyLinearVelocity = S.pv
			S.stepReq = 2
		else
			S.stepReq = 0
		end
		return
	end
	if S.mode ~= "play" or S.paused then return end
	local total = totalTime()
	-- Playback timeline is independent from the recording Slow Motion scale.
	S.gt += dt * curMul() * (S.rev and -1 or 1)
	if S.gt >= total then
		if S.loop and not S.rev then
			S.gt = 0
		else
			S.gt = total
			applyAt(S.gt)
			finishPlayback()
			return
		end
	elseif S.gt <= 0 and S.rev then
		if S.loop then
			S.gt = total
		else
			S.gt = 0
			applyAt(S.gt)
			finishPlayback()
			return
		end
	end
	applyAt(S.gt)
end)

conns[#conns + 1] = RunService.PostSimulation:Connect(function(dt)
	if S.stepReq == 2 then
		local _, h, r = chr()
		if r and S.mode == "record" then
			local v = r.AssemblyLinearVelocity
			S.pv = v
			r.Anchored = true
			r.AssemblyLinearVelocity = Vector3.zero
			-- Keep the recorder clock independent from S.scale: slow motion changes the world, not elapsed real time.
			S.gt += dt
			pushFrame(h, r, v)
		end
		S.stepRemaining -= 1
		S.stepReq = S.stepRemaining > 0 and 1 or 0
	elseif S.mode == "record" and not S.paused then
		local _, h, r = chr()
		if r then
			-- Real-time timestamps make a 0.50x recording replay correctly at 1.00x.
			S.gt += dt
			pushFrame(h, r)
		end
	end

	local gsrc = (S.ghostMode == 1 and S.ghostFrames) or (S.ghostMode == 2 and S.best) or nil
	if S.mode == "record" and gsrc and #gsrc > 0 then
		if not ghost then makeGhost() end
		if ghost then
			local a, b, k = sample(gsrc, S.gt)
			if a then ghost:PivotTo((b and k > 0) and a.cf:Lerp(b.cf, k) or a.cf) end
		end
	elseif ghost then
		killGhost()
	end

	if S.mode == "record" and not S.paused then
		autoAcc += dt
		if autoAcc > 30 then
			autoAcc = 0
			autosave()
		end
	end

	partAcc += dt
	if slowOn and partAcc > 1.5 then partAcc = 0; setParticles() end

	acc += dt
	if acc > 0.1 then
		acc = 0
		local total = totalTime()
		local m = ({ idle = "ожидание", record = "ЗАПИСЬ", play = "ВОСПРОИЗВЕДЕНИЕ" })[S.mode]
		status.Text = ("%s%s\nt = %.2f / %.2f c  |  кадров: %d  |  x%.2f%s"):format(m, S.paused and " (пауза)" or "", S.gt, total, #S.frames, S.scale, S.bestTime and ("  ⭐%.2f"):format(S.bestTime) or "")
		progFill.Size = UDim2.fromScale(total > 0 and math.clamp(S.gt / total, 0, 1) or 0, 1)

		if S.trail then
			if (#S.frames ~= trailN or S.frames[#S.frames] ~= trailLast)
				and not (S.mode == "record" and not S.paused) then
				drawTrail()
			end
		elseif trailFolder then
			clearTrail()
		end

		if os.clock() > toastUntil then
			msg.Text = hint()
			msg.TextColor3 = Color3.fromRGB(255, 214, 120)
		end

	end
end)

local CAMERA_BIND_NAME = "cocosTASCamera"
pcall(function() RunService:UnbindFromRenderStep(CAMERA_BIND_NAME) end)
RunService:BindToRenderStep(CAMERA_BIND_NAME, Enum.RenderPriority.Camera.Value + 1, function()
	local cam = workspace.CurrentCamera
	if not cam or not S.cam then return end
	if S.mode == "record" and not S.paused then
		local latest = S.frames[#S.frames]
		if latest then
			latest.cam = cam.CFrame
			latest.fov = cam.FieldOfView
		end
	elseif S.mode == "play" then
		local _, _, a, b, k = interpolate(S.frames, S.gt)
		if a and a.cam then
			if not S.camPrev then
				S.camPrev = cam.CameraType
				S.camFovPrev = cam.FieldOfView
			end
			cam.CameraType = Enum.CameraType.Scriptable
			cam.CFrame = (b and b.cam and k > 0) and a.cam:Lerp(b.cam, k) or a.cam
			if a.fov then
				cam.FieldOfView = b and b.fov and (a.fov + (b.fov - a.fov) * k) or a.fov
			end
		end
	end
end)

local function hookChar(c)
	local h = c:WaitForChild("Humanoid", 5)
	if not h then return end
	h.Died:Connect(function()
		if S.mode == "record" and S.autoRew then
			S.dead = true
			notify("Смерть - откат после респавна")
		end
	end)
end
if lp.Character then task.spawn(hookChar, lp.Character) end
conns[#conns + 1] = lp.CharacterAdded:Connect(function(c)
	task.spawn(hookChar, c)
	S.paused = false
	S.stepReq = 0
	if S.mode == "record" and S.dead then
		S.dead = false
		task.spawn(function()
			local t = 0
			repeat task.wait(0.1); t += 0.1 until chr() or t > 5
			task.wait(0.25)
			rewindSec(CFG.DeathRewind)
		end)
	else
		stopAll()
	end
end)

conns[#conns + 1] = UIS.InputBegan:Connect(function(i, gp)
	if gp or UIS:GetFocusedTextBox() then return end
	local k = i.KeyCode
	if k == Enum.KeyCode.R then toggleRec()
	elseif k == Enum.KeyCode.P then
		if S.mode == "play" then togglePause() else togglePlay() end
	elseif k == Enum.KeyCode.O then stopAll()
	elseif k == Enum.KeyCode.Comma then stepFrame(-1)
	elseif k == Enum.KeyCode.Period then stepFrame(1)
	elseif k == Enum.KeyCode.Z then rewindSec(0.2)
	elseif k == Enum.KeyCode.X then rewindSec(0.4)
	elseif k == Enum.KeyCode.F1 then
		local shouldOpen = not main.Visible
		menuManualVisible = shouldOpen
		menuForceVisible = shouldOpen
		refreshUI()
	end
end)

loadSaveCatalog()
refreshSaveList()
refreshUI()
notify("cocosTAS готов - нажми ЗАПИСЬ")
