// 银河铁道之夜 · 同页摄像头 / 手势输入。所有识别在浏览器本地运行。
// Frame contract is shared with exhibit.js; no WebSocket or fetch interception.
(function () {
  'use strict';
  if (window.__CFTrackerMobile && window.__CFTrackerMobile.version === 'night-train-2') return;
  var scriptURL = document.currentScript && document.currentScript.src;
  var VENDOR_BASE = (window.__CFTrackerVendorBase || './interaction/vendor').replace(/\/+$/, '');
  // Resolve imports against the page, rather than camera.js's own module directory.
  VENDOR_BASE = new URL(VENDOR_BASE + '/', document.baseURI).href.replace(/\/+$/, '');
  var UA = navigator.userAgent || '';
  var IS_MOBILE = /Android|iPhone|iPad|iPod/i.test(UA) || (/Macintosh/i.test(UA) && navigator.maxTouchPoints > 1);
  var LOW_END = (typeof navigator.deviceMemory === 'number' && navigator.deviceMemory <= 4) ||
    /Android\s+[4-8]\./.test(UA) || (/Android/i.test(UA) && navigator.hardwareConcurrency <= 4);
  var MODEL_INTERVALS = { gesture: LOW_END ? 100 : 70, face: LOW_END ? 300 : 200, pose: LOW_END ? 500 : 333 };
  var MODEL_TTL = { gesture: 420, face: 800, pose: 1200 };
  var CAM_W = LOW_END ? 480 : 640, CAM_H = LOW_END ? 360 : 480;
  var PINCH_DIST = .05, FIST_RATIO = 1, WAVE_WINDOW_MS = 800, WAVE_REVERSALS = 3;
  var WAVE_RANGE = .15, WAVE_COOLDOWN_MS = 1500, FINGER_RATIO = 1.15, VEL_EMA = .5;
  var GAZE_EMA = .55, GAZE_CAL_N = 16, BLINK_TH = .55, COMBO_HOLD_MS = 130;
  var state = 'idle', running = false, desired = true, session = null, generation = 0;
  var video = null, pipCanvas = null, pipCtx = null, ui = {}, rafId = 0;
  var selectedDevice = '', explicitDevice = false, devices = [], deviceRevision = 0;
  var modulePromise = null, visionPromise = null, hasGPU = null;
  var faceConnections = { outline: [], eyes: [], irises: [], lips: [] };
  var overlayState = { hands: {}, face: null, pose: null, lastAt: 0 };
  var stats = { frames: 0, hz: 0, lastFrameAt: 0, tier: LOW_END ? 'low' : 'std', models: { gesture: false, face: false, pose: false }, delegate: null,
    performance: { gesture: { count: 0, ms: 0 }, face: { count: 0, ms: 0 }, pose: { count: 0, ms: 0 }, scale: 1 } };
  window.__cfSoloFrame = emptyFrame();

  function warn() { console.warn.apply(console, ['[night-train-camera]'].concat([].slice.call(arguments))); }
  function emptyFrame() {
    return { type: 'track', t: Date.now(), hands: [], handsSpread: 0, face: null,
      body: { visible: false }, wave: false, eyes: { gx: 0, gy: 0, blink: false }, combo: null };
  }
  // ── 手势判定（复刻 tracker.html）──
  function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }
  function isPinch(lm) { return dist(lm[4], lm[8]) < PINCH_DIST; }
  function isFist(lm) {
    var wrist = lm[0];
    var pairs = [[8, 5], [12, 9], [16, 13], [20, 17]]; // [指尖, 指根]
    return pairs.every(function (pr) { return dist(lm[pr[0]], wrist) < dist(lm[pr[1]], wrist) * FIST_RATIO; });
  }

  // wave: 每个手槽位维护一段 (t, x) 历史，窗内方向反转 ≥3 且振幅 >0.15
  var waveHist = [[], []];
  var waveCooldownUntil = 0;
  function detectWave(slot, x, now) {
    var h = waveHist[slot];
    h.push({ t: now, x: x });
    while (h.length && now - h[0].t > WAVE_WINDOW_MS) h.shift();
    if (now < waveCooldownUntil || h.length < 6) return false;
    var reversals = 0, lastDir = 0, min = 1, max = 0;
    for (var i = 1; i < h.length; i++) {
      var dx = h[i].x - h[i - 1].x;
      if (h[i].x < min) min = h[i].x;
      if (h[i].x > max) max = h[i].x;
      var dir = Math.abs(dx) > 0.008 ? (dx > 0 ? 1 : -1) : 0; // 死区防抖
      if (dir && lastDir && dir !== lastDir) reversals++;
      if (dir) lastDir = dir;
    }
    if (reversals >= WAVE_REVERSALS && (max - min) > WAVE_RANGE) {
      waveCooldownUntil = now + WAVE_COOLDOWN_MS;
      h.length = 0;
      return true;
    }
    return false;
  }

  // fingers: 5 指伸直标记 [拇指,食指,中指,无名指,小指]
  function fingerStates(lm) {
    var wrist = lm[0];
    function ext(tip, mcp) { return dist(lm[tip], wrist) > dist(lm[mcp], wrist) * FINGER_RATIO ? 1 : 0; }
    return [
      dist(lm[4], lm[17]) > dist(lm[3], lm[17]) * FINGER_RATIO ? 1 : 0, // 拇指
      ext(8, 5), ext(12, 9), ext(16, 13), ext(20, 17),                  // 食/中/无名/小
    ];
  }

  // vel: 每手槽位 EMA 平滑速度（镜像坐标下本帧相对上帧的位移）
  var handVel = [null, null];
  function updateVel(slot, x, y) {
    var prev = handVel[slot];
    var dx = 0, dy = 0;
    if (prev) {
      dx = VEL_EMA * (x - prev.x) + (1 - VEL_EMA) * prev.dx;
      dy = VEL_EMA * (y - prev.y) + (1 - VEL_EMA) * prev.dy;
    }
    handVel[slot] = { x: x, y: y, dx: dx, dy: dy };
    return { dx: +dx.toFixed(3), dy: +dy.toFixed(3) };
  }
  function resetSlot(i) { waveHist[i].length = 0; handVel[i] = null; } // 手消失清空该槽位

  // ── 眼动 gaze：虹膜中心相对眼眶中心/半眼宽的归一化偏移（x 已做 1-x 镜像统一）──
  var gaze = {
    emaGx: 0, emaGy: 0, has: false,
    calN: 0, calSx: 0, calSy: 0,
    bGx: null, bGy: null,
    blink: false, blinkRaw: false, blinkAt: 0,
  };
  function eyeGaze(lm, iIris, iA, iB) { // 单眼: (虹膜 - 两眼角中点) / 半眼宽
    var mx = function (i) { return 1 - lm[i].x; }; // 镜像统一（与帧/预览一致）
    var ax = mx(iA), bx = mx(iB);
    var half = Math.abs(ax - bx) / 2 || 1e-6;
    return {
      gx: (mx(iIris) - (ax + bx) / 2) / half,
      gy: (lm[iIris].y - (lm[iA].y + lm[iB].y) / 2) / half,
    };
  }
  function updateGaze(faceRes, now) { // Update only on a fresh face sample.
    var raw = false;
    var cats = faceRes && faceRes.faceBlendshapes && faceRes.faceBlendshapes[0]
      ? faceRes.faceBlendshapes[0].categories : null;
    if (cats) {
      var L = 0, R = 0;
      for (var i = 0; i < cats.length; i++) {
        if (cats[i].categoryName === 'eyeBlinkLeft') L = cats[i].score;
        else if (cats[i].categoryName === 'eyeBlinkRight') R = cats[i].score;
      }
      var threshold = gaze.blink ? .35 : BLINK_TH;
      raw = L > threshold && R > threshold;
    }
    // Hysteresis rather than multi-frame debounce: face inference is 3–5 Hz, so a
    // second closed sample would miss normal blinks. A detected blink releases on the next open sample.
    gaze.blink = gaze.blinkRaw = raw; gaze.blinkAt = now;

    var lm = faceRes && faceRes.faceLandmarks && faceRes.faceLandmarks[0];
    if (!lm || lm.length < 478) return; // Invalid iris data is not used for calibration or output.
    var r = eyeGaze(lm, 468, 33, 133);   // 右眼虹膜 468（眼角 33 外 / 133 内）
    var l = eyeGaze(lm, 473, 362, 263);  // 左眼虹膜 473（眼角 362 内 / 263 外）
    var gx = (r.gx + l.gx) / 2, gy = (r.gy + l.gy) / 2; // 双眼平均
    if (gaze.has) {
      gaze.emaGx = GAZE_EMA * gx + (1 - GAZE_EMA) * gaze.emaGx;
      gaze.emaGy = GAZE_EMA * gy + (1 - GAZE_EMA) * gaze.emaGy;
    } else { gaze.emaGx = gx; gaze.emaGy = gy; gaze.has = true; }
    if (gaze.calN < GAZE_CAL_N) { // Lock the baseline after GAZE_CAL_N valid samples.
      gaze.calSx += gx; gaze.calSy += gy;
      if (++gaze.calN === GAZE_CAL_N) { gaze.bGx = gaze.calSx / GAZE_CAL_N; gaze.bGy = gaze.calSy / GAZE_CAL_N; }
    }
  }
  function gazeEyes() { // 帧内用：减基线归零，保留 3 位；校准完成前输出 0
    var gx = gaze.bGx === null ? 0 : gaze.emaGx - gaze.bGx;
    var gy = gaze.bGy === null ? 0 : gaze.emaGy - gaze.bGy;
    return { gx: +gx.toFixed(3), gy: +gy.toFixed(3), blink: gaze.blink };
  }

  // ── 双手组合 combo：两手同时在位时按各自形态分派，稳定 130ms 才写入（迟滞）──
  var COMBO_MAP = {
    'fist+fist': 'double-fist', 'palm+palm': 'double-palm',
    'pinch+pinch': 'double-pinch', 'fist+palm': 'fist-palm',
  };
  var comboOut = null, comboCand = null, comboSince = 0, primaryHandId = null;
  function handShape(h) { // 形态优先级 fist > pinch > palm（握拳时拇指食指常贴近）
    if (h.fist) return 'fist';
    if (h.pinch) return 'pinch';
    var f = h.fingers;
    return f[1] && f[2] && f[3] && f[4] ? 'palm' : null;
  }
  function updateCombo(hands, now) { // Single/no hand releases immediately; shape changes settle for 130 ms.
    if (hands.length < 2) { comboOut = comboCand = null; comboSince = now; return null; }
    var target = null;
    if (hands.length === 2) {
      var a = handShape(hands[0]), b = handShape(hands[1]);
      if (a && b) target = COMBO_MAP[[a, b].sort().join('+')] || null;
    }
    if (target !== comboCand) { comboCand = target; comboSince = now; }
    if (comboCand !== comboOut && now - comboSince >= COMBO_HOLD_MS) comboOut = comboCand;
    return comboOut;
  }

  // ── 数据组装：x 统一镜像（1 - x），像照镜子；字段与 tracker.html 逐一对齐 ──
  function pinchAperture(lm) { return +(dist(lm[4], lm[8]) / (dist(lm[0], lm[9]) || 1e-6)).toFixed(3); }
  function buildPayload(handsRes, faceRes, poseRes, cachedHands) {
    var now = performance.now();
    var hands = [];
    var lms = handsRes && handsRes.landmarks || [];
    var handed = handsRes ? (handsRes.handednesses ?? handsRes.handedness ?? []) : [];
    var wave = false, seenSlots = [false, false];
    for (var i = 0; !cachedHands && i < Math.min(lms.length, 2); i++) {
      var lm = lms[i];
      var palm = lm[9]; // 中指根作为手掌中心
      var x = 1 - palm.x, y = palm.y;
      var g = (handsRes && handsRes.gestures ? handsRes.gestures[i] : null)?.[0] || null; // 官方手势 top1
      var hd = (handed[i] || null)?.[0] || null; // 左右手标签
      var slot = hd && hd.categoryName === 'Left' ? 0 : hd && hd.categoryName === 'Right' ? 1 : i;
      if (seenSlots[slot]) slot = 1 - slot;
      seenSlots[slot] = true;
      if (detectWave(slot, x, now)) wave = true;
      hands.push({
        id: slot, x: +x.toFixed(4), y: +y.toFixed(4), pinch: isPinch(lm), fist: isFist(lm), ap: pinchAperture(lm),
        hand: hd ? hd.categoryName : null,        // "Left"/"Right"（标签相对图像，镜像下直接透传）
        gesture: g && g.categoryName !== 'None' ? g.categoryName : null,
        gscore: g ? +g.score.toFixed(3) : 0,
        fingers: fingerStates(lm),                // [拇,食,中,无,小] 0/1 伸直标记
        vel: updateVel(slot, x, y),                  // {dx,dy} EMA 平滑
      });
    }
    if (!cachedHands) {
      for (var j = 0; j < 2; j++) if (!seenSlots[j]) resetSlot(j);
      hands.sort(function (a, b) { return a.id - b.id; });
      var primaryIndex = hands.findIndex(function (hand) { return hand.id === primaryHandId; });
      if (primaryIndex > 0) hands.unshift(hands.splice(primaryIndex, 1)[0]);
      primaryHandId = hands.length ? hands[0].id : null;
    }

    if (cachedHands) hands = cachedHands.hands;
    var handsSpread = 0;
    if (hands.length === 2) handsSpread = +Math.hypot(hands[0].x - hands[1].x, hands[0].y - hands[1].y).toFixed(4);

    // Original tracker torso: center of visible shoulders/hips; face nose prefers the face model.
    var face = null, body = { visible: false };
    var flm = faceRes && faceRes.faceLandmarks && faceRes.faceLandmarks[0];
    var pose = poseRes && poseRes.landmarks && poseRes.landmarks[0];
    if (flm && flm[1]) face = { x: +(1 - flm[1].x).toFixed(4), y: +flm[1].y.toFixed(4) };
    if (pose) {
      if (!face && visiblePoint(pose[0])) face = { x: +(1 - pose[0].x).toFixed(4), y: +pose[0].y.toFixed(4) };
      var torso = [pose[11], pose[12], pose[23], pose[24]].filter(visiblePoint);
      if (torso.length >= 2) body = {
        visible: true,
        x: +(1 - torso.reduce(function (sum, p) { return sum + p.x; }, 0) / torso.length).toFixed(4),
        y: +(torso.reduce(function (sum, p) { return sum + p.y; }, 0) / torso.length).toFixed(4)
      };
    }
    return {
      type: 'track', t: Date.now(), hands: hands, handsSpread: handsSpread, face: face, body: body,
      wave: wave, eyes: flm && flm.length >= 478 ? gazeEyes() : { gx: 0, gy: 0, blink: false },
      combo: cachedHands ? cachedHands.combo : updateCombo(hands, now)
    };
  }
  function visiblePoint(point) { return !!point && (point.visibility === undefined || point.visibility > .4); }

  function deliver(frame, count) {
    window.__cfSoloFrame = frame;
    if (count !== false) {
      if (!stats.frames) stats.t0 = performance.now();
      stats.frames++;
      stats.lastFrameAt = performance.now();
      if (stats.lastFrameAt > stats.t0) stats.hz = +((stats.frames - 1) * 1000 / (stats.lastFrameAt - stats.t0)).toFixed(1);
    }
    (document.body || document.documentElement).dispatchEvent(new CustomEvent('exhibit:solo-frame', { bubbles: true, detail: frame }));
  }
  function clearTracking() {
    resetSlot(0); resetSlot(1);
    comboOut = comboCand = null; comboSince = waveCooldownUntil = 0; primaryHandId = null;
    gaze = { emaGx: 0, emaGy: 0, has: false, calN: 0, calSx: 0, calSy: 0,
      bGx: null, bGy: null, blink: false, blinkRaw: false, blinkAt: 0 };
    // An explicit empty frame releases exhibit.js's drag, fist, combo and gaze states.
    deliver(emptyFrame(), false);
    stats.hz = 0; stats.frames = 0; stats.models.gesture = stats.models.face = stats.models.pose = false;
    ['gesture', 'face', 'pose'].forEach(function (kind) { stats.performance[kind] = { count: 0, ms: 0 }; });
    stats.performance.scale = 1;
    stats.delegate = null;
    overlayState = { hands: {}, face: null, pose: null, lastAt: 0 };
    if (pipCtx) pipCtx.clearRect(0, 0, pipCanvas.width, pipCanvas.height);
    if (ui.root) ui.root.dataset.tracking = 'false';
  }
  function setState(next, message) {
    state = next;
    if (!ui.root) return;
    ui.root.dataset.state = next;
    ui.status.textContent = message || '';
    ui.btn.setAttribute('aria-pressed', String(next === 'running' || next === 'starting'));
    ui.btn.setAttribute('aria-label', next === 'running' || next === 'starting' ? 'Turn camera off' : 'Turn camera on');
  }
  function isCurrent(s) { return session === s && s.generation === generation && !s.cancelled; }
  function stopTracks(stream) {
    if (stream) stream.getTracks().forEach(function (track) { try { track.stop(); } catch (_) {} });
  }
  function closeModel(model) { if (model) { try { model.close(); } catch (_) {} } }
  function dispose(s) {
    if (!s) return;
    s.cancelled = true;
    stopTracks(s.stream);
    closeModel(s.gesture); closeModel(s.face); closeModel(s.pose);
    s.stream = s.gesture = s.face = s.pose = null;
  }
  function halt(next, message, keepDesired) {
    if (!keepDesired) desired = false;
    generation++;
    running = false;
    if (rafId) cancelAnimationFrame(rafId);
    rafId = 0;
    dispose(session); session = null;
    if (video) { video.pause(); video.srcObject = null; }
    clearTracking();
    setState(next || 'idle', message);
  }
  function stop() { halt('idle'); }
  function canUseCamera() {
    return window.isSecureContext && navigator.mediaDevices && typeof navigator.mediaDevices.getUserMedia === 'function';
  }
  function cameraError(err) {
    var name = String(err && (err.name || err.message) || '');
    if (/NotAllowed|Permission|Security/i.test(name)) return 'No access';
    if (/NotFound|DevicesNotFound/i.test(name)) return 'No camera';
    if (/NotReadable|TrackStart/i.test(name)) return 'Camera busy';
    return 'Unavailable';
  }
  function preferredDevice(list) {
    if (IS_MOBILE) return null;
    return list.find(function (d) { return /usb|external|外接|外置|罗技|logitech/i.test(d.label); }) || null;
  }
  function renderDevices() {
    if (!ui.select) return;
    ui.select.replaceChildren();
    var defaultOption = document.createElement('option');
    defaultOption.value = ''; defaultOption.textContent = IS_MOBILE ? 'Front camera' : 'Automatic';
    ui.select.appendChild(defaultOption);
    devices.forEach(function (d, i) {
      if (!d.deviceId) return;
      var option = document.createElement('option');
      option.value = d.deviceId; option.textContent = d.label || 'Camera ' + (i + 1);
      ui.select.appendChild(option);
    });
    ui.select.value = selectedDevice;
  }
  async function refreshDevices() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.enumerateDevices) return devices;
    var rev = ++deviceRevision;
    try {
      var list = (await navigator.mediaDevices.enumerateDevices()).filter(function (d) { return d.kind === 'videoinput'; });
      if (rev === deviceRevision) { devices = list; renderDevices(); }
      return list;
    } catch (_) { return devices; }
  }
  function constraints(id) {
    var opts = { width: { ideal: CAM_W }, height: { ideal: CAM_H }, frameRate: { ideal: 24, max: 30 } };
    if (id) opts.deviceId = { exact: id };
    else if (IS_MOBILE) opts.facingMode = { ideal: 'user' };
    return { video: opts, audio: false };
  }
  function supportsGPU() {
    if (hasGPU !== null) return hasGPU;
    try {
      var canvas = document.createElement('canvas');
      var gl = canvas.getContext('webgl2');
      hasGPU = !!gl;
      if (gl) { var lose = gl.getExtension('WEBGL_lose_context'); if (lose) lose.loseContext(); }
    } catch (_) { hasGPU = false; }
    return hasGPU;
  }
  async function getVision() {
    if (!modulePromise) modulePromise = import(VENDOR_BASE + '/vision_bundle.mjs').catch(function (e) { modulePromise = null; throw e; });
    var mod = await modulePromise;
    var faceClass = mod.FaceLandmarker;
    faceConnections.outline = faceClass.FACE_LANDMARKS_FACE_OVAL || [];
    faceConnections.eyes = (faceClass.FACE_LANDMARKS_LEFT_EYE || []).concat(faceClass.FACE_LANDMARKS_RIGHT_EYE || []);
    faceConnections.irises = (faceClass.FACE_LANDMARKS_LEFT_IRIS || []).concat(faceClass.FACE_LANDMARKS_RIGHT_IRIS || []);
    faceConnections.lips = faceClass.FACE_LANDMARKS_LIPS || [];
    if (!visionPromise) visionPromise = mod.FilesetResolver.forVisionTasks(VENDOR_BASE + '/wasm').catch(function (e) { visionPromise = null; throw e; });
    return { mod: mod, vision: await visionPromise };
  }
  async function createModel(s, resources, kind) {
    var delegate = supportsGPU() ? 'GPU' : 'CPU';
    var factory = kind === 'gesture' ? resources.mod.GestureRecognizer : kind === 'face' ? resources.mod.FaceLandmarker : resources.mod.PoseLandmarker;
    function create(which) {
      var opts = { baseOptions: { modelAssetPath: VENDOR_BASE + '/models/' + (kind === 'gesture' ? 'gesture_recognizer.task' : kind === 'face' ? 'face_landmarker.task' : 'pose_landmarker_lite.task'), delegate: which }, runningMode: 'VIDEO' };
      if (kind === 'gesture') opts.numHands = 2;
      else if (kind === 'face') { opts.numFaces = 1; opts.outputFaceBlendshapes = true; }
      else { opts.numPoses = 1; opts.outputSegmentationMasks = false; }
      return factory.createFromOptions(resources.vision, opts);
    }
    var model;
    try { model = await create(delegate); }
    catch (err) {
      if (!isCurrent(s) || delegate === 'CPU') throw err;
      delegate = 'CPU'; model = await create('CPU');
    }
    if (!isCurrent(s)) { closeModel(model); return null; }
    if (kind === 'gesture') stats.delegate = delegate;
    s[kind] = model;
    stats.models[kind] = true;
    return model;
  }
  function start() {
    desired = true;
    if (!ui.root && document.body) injectUI();
    if (document.hidden) { setState('paused'); return Promise.resolve(false); }
    if (session && !session.cancelled) return session.promise || Promise.resolve(running);
    if (!canUseCamera()) {
      desired = false;
      setState('failed', window.isSecureContext ? 'Unavailable' : 'HTTPS only');
      return Promise.resolve(false);
    }
    var s = { generation: ++generation, cancelled: false, stream: null, gesture: null, face: null, pose: null,
      lastVideoTime: -1, errors: { gesture: 0, face: 0, pose: 0 }, timestamps: { gesture: 0, face: 0, pose: 0 },
      due: { gesture: 0, face: 0, pose: 0 }, results: { gesture: null, face: null, pose: null },
      sampledAt: { gesture: 0, face: 0, pose: 0 }, handFrame: null, lastDraw: 0 };
    session = s;
    clearTracking();
    setState('starting', 'Starting');
    s.promise = runStart(s);
    return s.promise;
  }
  async function runStart(s) {
    var stage = 'camera';
    try {
      var list = await refreshDevices();
      if (!isCurrent(s)) return false;
      var preferred = !explicitDevice && preferredDevice(list);
      var deviceId = selectedDevice || (preferred && preferred.deviceId) || '';
      var acquired;
      try { acquired = await navigator.mediaDevices.getUserMedia(constraints(deviceId)); }
      catch (err) {
        if (!isCurrent(s)) return false;
        if (deviceId && /NotFound|Overconstrained/.test(err.name)) acquired = await navigator.mediaDevices.getUserMedia(constraints(''));
        else throw err;
      }
      if (!isCurrent(s)) { stopTracks(acquired); return false; }
      s.stream = acquired;
      // Device labels become available after permission. Prefer an external USB camera on desktop.
      list = await refreshDevices();
      if (!isCurrent(s)) return false;
      preferred = !explicitDevice && preferredDevice(list);
      var currentId = acquired.getVideoTracks()[0].getSettings().deviceId || '';
      if (preferred && preferred.deviceId && preferred.deviceId !== currentId) {
        var usbStream;
        try { usbStream = await navigator.mediaDevices.getUserMedia(constraints(preferred.deviceId)); }
        catch (_) { /* Keep the usable default camera if the preferred device is busy. */ }
        if (!isCurrent(s)) { stopTracks(usbStream); return false; }
        if (usbStream) { stopTracks(acquired); acquired = s.stream = usbStream; }
      }
      selectedDevice = acquired.getVideoTracks()[0].getSettings().deviceId || deviceId;
      renderDevices();
      acquired.getTracks().forEach(function (track) {
        track.addEventListener('ended', function () { if (isCurrent(s)) halt('failed', 'Camera lost'); });
      });
      video.srcObject = acquired;
      await video.play();
      if (!isCurrent(s)) return false;
      stage = 'model';
      var resources = await getVision();
      if (!isCurrent(s)) return false;
      await createModel(s, resources, 'gesture');
      if (!isCurrent(s)) return false;
      // Optional models fail independently so a missing face/pose model never disables hands.
      try { await createModel(s, resources, 'face'); }
      catch (err) { if (isCurrent(s)) warn('Face model unavailable; continuing hand tracking', err && err.message); }
      if (!isCurrent(s)) return false;
      try { await createModel(s, resources, 'pose'); }
      catch (err) { if (isCurrent(s)) warn('Pose model unavailable; continuing other tracking', err && err.message); }
      if (!isCurrent(s)) return false;
      running = true;
      setState('running', s.face && s.pose ? '' : 'Partial tracking');
      loop(s);
      return true;
    } catch (err) {
      if (!isCurrent(s)) return false;
      warn(stage === 'camera' ? 'Camera startup failed' : 'Tracking startup failed', err && (err.name || err.message));
      halt('failed', stage === 'camera' ? cameraError(err) : 'Unavailable');
      return false;
    }
  }
  function monoTs(s, key, t) { s.timestamps[key] = Math.max(t, s.timestamps[key] + .1); return s.timestamps[key]; }
  function modelInterval(kind) { return MODEL_INTERVALS[kind] * stats.performance.scale; }
  function nextModel(s, now) {
    var chosen = null, best = -Infinity;
    ['gesture', 'face', 'pose'].forEach(function (kind) {
      if (!s[kind] || now < s.due[kind]) return;
      // Earliest overdue work wins, with a small hand preference and no face/pose starvation.
      var score = 1 + (now - s.due[kind]) / modelInterval(kind) + (kind === 'gesture' ? .4 : 0);
      if (score > best) { best = score; chosen = kind; }
    });
    return chosen;
  }
  function notePerformance(kind, duration) {
    var p = stats.performance[kind];
    p.ms = p.count ? p.ms * .8 + duration * .2 : duration;
    p.count++;
    var load = ['gesture', 'face', 'pose'].reduce(function (sum, key) {
      return sum + (stats.models[key] ? stats.performance[key].ms / MODEL_INTERVALS[key] : 0);
    }, 0);
    // Target at most ~45% main-thread inference work. Slow devices retain all model types.
    var target = Math.max(1, Math.min(3.5, load / .45));
    stats.performance.scale = stats.performance.scale * .8 + target * .2;
  }
  function expireResults(s, now) {
    var changed = false;
    ['gesture', 'face', 'pose'].forEach(function (kind) {
      var ttl = Math.min(MODEL_TTL[kind] * 2, Math.max(MODEL_TTL[kind], modelInterval(kind) * 2.5));
      if (s.results[kind] && now - s.sampledAt[kind] > ttl) {
        s.results[kind] = null;
        if (kind === 'face') { gaze.has = false; gaze.blink = gaze.blinkRaw = false; }
        if (kind === 'gesture') { s.handFrame = null; comboOut = comboCand = null; }
        changed = true;
      }
    });
    return changed;
  }
  function publishResults(s, updateHands) {
    var frame = buildPayload(s.results.gesture, s.results.face, s.results.pose, updateHands ? null : s.handFrame);
    if (updateHands || !s.handFrame) s.handFrame = frame;
    deliver(frame);
    ui.root.dataset.tracking = String(!!(frame.hands.length || frame.face || frame.body.visible));
  }
  function loop(s) {
    if (!isCurrent(s) || !running) return;
    rafId = requestAnimationFrame(function () { loop(s); });
    var now = performance.now();
    var expired = expireResults(s, now);
    var freshVideo = video.readyState >= 2 && video.currentTime !== s.lastVideoTime;
    var kind = freshVideo ? nextModel(s, now) : null;
    if (kind) {
      s.lastVideoTime = video.currentTime;
      var startedAt = performance.now();
      try {
        // Exactly one synchronous MediaPipe call per animation frame.
        var result = kind === 'gesture' ? s.gesture.recognizeForVideo(video, monoTs(s, kind, now)) :
          s[kind].detectForVideo(video, monoTs(s, kind, now));
        s.results[kind] = result;
        s.sampledAt[kind] = now;
        s.errors[kind] = 0;
        if (kind === 'face') {
          if (result.faceLandmarks && result.faceLandmarks.length) updateGaze(result, now);
          else { gaze.has = false; gaze.blink = gaze.blinkRaw = false; }
        }
        publishResults(s, kind === 'gesture');
      } catch (err) {
        s.results[kind] = null;
        if (kind === 'face') { gaze.has = false; gaze.blink = gaze.blinkRaw = false; }
        if (kind === 'gesture') { s.handFrame = null; comboOut = comboCand = null; }
        publishResults(s, kind === 'gesture');
        if (++s.errors[kind] >= 8) {
          if (kind === 'gesture') { warn('Hand tracking paused', err && err.message); halt('failed', 'Unavailable'); return; }
          warn(kind + ' tracking unavailable; continuing other models', err && err.message);
          closeModel(s[kind]); s[kind] = null; stats.models[kind] = false;
          setState('running', 'Partial tracking');
        }
      }
      notePerformance(kind, performance.now() - startedAt);
      // Date the next run from completion; a slow inference always yields a render opportunity.
      s.due[kind] = performance.now() + modelInterval(kind);
    } else if (expired) publishResults(s, !s.results.gesture);
    if (now - s.lastDraw >= (LOW_END ? 50 : 30) || kind || expired) {
      drawPip(s.results.gesture, s.results.face, s.results.pose);
      s.lastDraw = now;
    }
  }

  var HAND_BONES = [[0,1],[1,2],[2,3],[3,4],[0,5],[5,6],[6,7],[7,8],[5,9],[9,10],[10,11],[11,12],[9,13],[13,14],[14,15],[15,16],[13,17],[17,18],[18,19],[19,20],[0,17]];
  function previewPoint(lm, w, h, sourceW, sourceH) {
    // Same centered cover crop and mirror as the video element; works with 4:3, 16:9 and portrait sources.
    var scale = Math.max(w / sourceW, h / sourceH);
    return { x: (1 - lm.x) * sourceW * scale - (sourceW * scale - w) / 2,
      y: lm.y * sourceH * scale - (sourceH * scale - h) / 2 };
  }
  var POSE_BONES = [[11,12],[11,13],[13,15],[12,14],[14,16],[11,23],[12,24],[23,24],[23,25],[25,27],[24,26],[26,28],[27,29],[29,31],[27,31],[28,30],[30,32],[28,32]];
  function smoothLandmarks(previous, target, dt, tau) {
    if (!target || !target.length) return null;
    if (!previous || previous.length !== target.length) return target.map(function (p) { return Object.assign({}, p); });
    var alpha = 1 - Math.exp(-Math.min(dt, 250) / tau);
    return target.map(function (point, index) {
      var p = previous[index];
      return Object.assign({}, point, { x: p.x + (point.x - p.x) * alpha, y: p.y + (point.y - p.y) * alpha });
    });
  }
  function smoothOverlay(result, faceResult, poseResult, now) {
    var dt = overlayState.lastAt ? Math.max(0, now - overlayState.lastAt) : 0;
    overlayState.lastAt = now;
    var seen = {}, hands = [], handed = result && (result.handednesses || result.handedness) || [];
    (result && result.landmarks || []).forEach(function (landmarks, index) {
      var label = handed[index] && handed[index][0] && handed[index][0].categoryName;
      var key = label === 'Left' || label === 'Right' ? label : String(index);
      if (seen[key]) key += '-' + index;
      seen[key] = true;
      overlayState.hands[key] = smoothLandmarks(overlayState.hands[key], landmarks, dt, 60);
      hands.push(overlayState.hands[key]);
    });
    Object.keys(overlayState.hands).forEach(function (key) { if (!seen[key]) delete overlayState.hands[key]; });
    overlayState.face = smoothLandmarks(overlayState.face, faceResult && faceResult.faceLandmarks && faceResult.faceLandmarks[0], dt, 80);
    overlayState.pose = smoothLandmarks(overlayState.pose, poseResult && poseResult.landmarks && poseResult.landmarks[0], dt, 100);
    return { hands: hands, face: overlayState.face, pose: overlayState.pose };
  }
  function drawPip(result, faceResult, poseResult) {
    if (!pipCtx || !video.videoWidth || !video.videoHeight) return;
    var display = smoothOverlay(result, faceResult, poseResult, performance.now());
    var w = ui.root.clientWidth, h = ui.root.clientHeight, dpr = Math.min(window.devicePixelRatio || 1, 2);
    if (pipCanvas.width !== Math.round(w * dpr) || pipCanvas.height !== Math.round(h * dpr)) {
      pipCanvas.width = Math.round(w * dpr); pipCanvas.height = Math.round(h * dpr);
    }
    pipCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    pipCtx.clearRect(0, 0, w, h);
    var pose = display.pose;
    if (pose) {
      pipCtx.shadowBlur = 0; pipCtx.strokeStyle = 'rgba(255,255,255,.48)'; pipCtx.lineWidth = w < 200 ? .7 : 1;
      pipCtx.beginPath();
      POSE_BONES.forEach(function (bone) {
        if (!visiblePoint(pose[bone[0]]) || !visiblePoint(pose[bone[1]])) return;
        var a = previewPoint(pose[bone[0]], w, h, video.videoWidth, video.videoHeight);
        var b = previewPoint(pose[bone[1]], w, h, video.videoWidth, video.videoHeight);
        pipCtx.moveTo(a.x, a.y); pipCtx.lineTo(b.x, b.y);
      });
      pipCtx.stroke();
      pipCtx.fillStyle = 'rgba(255,255,255,.72)';
      [11,12,13,14,15,16,23,24,25,26,27,28].forEach(function (index) {
        if (!visiblePoint(pose[index])) return;
        var p = previewPoint(pose[index], w, h, video.videoWidth, video.videoHeight);
        pipCtx.beginPath(); pipCtx.arc(p.x, p.y, w < 200 ? 1 : 1.4, 0, Math.PI * 2); pipCtx.fill();
      });
    }
    var face = display.face;
    if (face) {
      // Contours only: no dense tessellation over the camera portrait.
      function faceEdges(edges, opacity) {
        pipCtx.strokeStyle = 'rgba(255,255,255,' + opacity + ')'; pipCtx.lineWidth = w < 200 ? .55 : .8;
        pipCtx.beginPath();
        edges.forEach(function (edge) {
          if (!face[edge.start] || !face[edge.end]) return;
          var a = previewPoint(face[edge.start], w, h, video.videoWidth, video.videoHeight);
          var b = previewPoint(face[edge.end], w, h, video.videoWidth, video.videoHeight);
          pipCtx.moveTo(a.x, a.y); pipCtx.lineTo(b.x, b.y);
        });
        pipCtx.stroke();
      }
      pipCtx.shadowBlur = 0;
      faceEdges(faceConnections.outline, .48); faceEdges(faceConnections.eyes, .64);
      faceEdges(faceConnections.lips, .38); faceEdges(faceConnections.irises, .85);
      pipCtx.fillStyle = 'rgba(255,255,255,.9)';
      [1, 468, 473].forEach(function (index) {
        if (!face[index]) return;
        var p = previewPoint(face[index], w, h, video.videoWidth, video.videoHeight);
        pipCtx.beginPath(); pipCtx.arc(p.x, p.y, index === 1 ? .8 : 1, 0, Math.PI * 2); pipCtx.fill();
      });
    }
    display.hands.forEach(function (lm) {
      var points = lm.map(function (p) { return previewPoint(p, w, h, video.videoWidth, video.videoHeight); });
      pipCtx.strokeStyle = 'rgba(255,255,255,.94)'; pipCtx.fillStyle = '#fff';
      pipCtx.shadowColor = 'rgba(4,8,18,.6)'; pipCtx.shadowBlur = 3;
      pipCtx.lineWidth = w < 200 ? 1 : 1.4;
      pipCtx.beginPath();
      HAND_BONES.forEach(function (bone) {
        pipCtx.moveTo(points[bone[0]].x, points[bone[0]].y);
        pipCtx.lineTo(points[bone[1]].x, points[bone[1]].y);
      });
      pipCtx.stroke();
      points.forEach(function (p) { pipCtx.beginPath(); pipCtx.arc(p.x, p.y, w < 200 ? 1.2 : 1.7, 0, Math.PI * 2); pipCtx.fill(); });
      if (isPinch(lm)) {
        pipCtx.beginPath();
        pipCtx.arc((points[4].x + points[8].x) / 2, (points[4].y + points[8].y) / 2, w < 200 ? 5 : 7, 0, Math.PI * 2);
        pipCtx.stroke();
      }
    });
  }
  function injectUI() {
    if (ui.root) return;
    var stylesheet = document.createElement('link');
    stylesheet.rel = 'stylesheet'; stylesheet.href = new URL('camera.css', scriptURL || new URL('./interaction/camera.js', document.baseURI)).href;
    document.head.appendChild(stylesheet);
    var root = document.createElement('aside');
    root.id = 'cf-camera'; root.dataset.state = 'idle'; root.setAttribute('aria-label', 'Camera');
    video = document.createElement('video');
    video.autoplay = true; video.muted = true; video.playsInline = true;
    video.setAttribute('playsinline', ''); video.setAttribute('muted', ''); video.setAttribute('aria-hidden', 'true');
    pipCanvas = document.createElement('canvas'); pipCanvas.setAttribute('aria-hidden', 'true'); pipCtx = pipCanvas.getContext('2d');
    var controls = document.createElement('div'); controls.className = 'cf-camera-controls';
    var dot = document.createElement('span'); dot.className = 'cf-camera-dot'; dot.setAttribute('aria-hidden', 'true');
    var status = document.createElement('span'); status.className = 'cf-camera-status'; status.setAttribute('role', 'status');
    var select = document.createElement('select'); select.hidden = true; select.setAttribute('aria-label', 'Select camera');
    var deviceBtn = document.createElement('button'); deviceBtn.type = 'button'; deviceBtn.setAttribute('aria-label', 'Select camera'); deviceBtn.setAttribute('aria-expanded', 'false');
    deviceBtn.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"><path d="M4 8a8 8 0 0 1 13-3l3 3M20 3v5h-5M20 16a8 8 0 0 1-13 3l-3-3M4 21v-5h5"/></svg>';
    var btn = document.createElement('button'); btn.type = 'button'; btn.setAttribute('aria-label', 'Turn camera on'); btn.setAttribute('aria-pressed', 'false');
    btn.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"><rect x="2" y="6" width="13" height="12" rx="2"/><path d="m15 10 6-3v10l-6-3"/><path class="cf-camera-off" d="M3 3 21 21"/></svg>';
    controls.append(dot, status, deviceBtn, btn); root.append(video, pipCanvas, controls, select); document.body.appendChild(root);
    ui = { root: root, btn: btn, deviceBtn: deviceBtn, select: select, dot: dot, status: status };
    ['pointerdown', 'pointerup', 'click', 'touchstart', 'touchend', 'wheel'].forEach(function (name) { root.addEventListener(name, function (event) { event.stopPropagation(); }); });
    btn.addEventListener('click', function () { if (state === 'starting' || running) stop(); else start(); });
    deviceBtn.addEventListener('click', function () {
      select.hidden = !select.hidden; deviceBtn.setAttribute('aria-expanded', String(!select.hidden));
      if (!select.hidden) { refreshDevices(); select.focus(); }
    });
    select.addEventListener('change', function () {
      selectedDevice = select.value; explicitDevice = !!selectedDevice;
      select.hidden = true; deviceBtn.setAttribute('aria-expanded', 'false');
      halt('idle'); start();
    });
    select.addEventListener('keydown', function (event) { if (event.key === 'Escape') { select.hidden = true; deviceBtn.setAttribute('aria-expanded', 'false'); deviceBtn.focus(); } });
    renderDevices();
  }
  function boot() {
    injectUI();
    if (navigator.mediaDevices && navigator.mediaDevices.addEventListener) navigator.mediaDevices.addEventListener('devicechange', refreshDevices);
    document.addEventListener('visibilitychange', function () {
      if (document.hidden) { if (desired) halt('paused', '', true); }
      else if (desired && state === 'paused') start();
    });
    window.addEventListener('pagehide', function () { halt('paused', '', true); });
    window.addEventListener('pageshow', function () { if (desired && state === 'paused' && !document.hidden) start(); });
    start();
  }
  var api = { start: start, stop: stop, stats: stats, version: 'night-train-2', refreshDevices: refreshDevices,
    selectDevice: function (id) { selectedDevice = id || ''; explicitDevice = !!id; halt('idle'); return start(); } };
  Object.defineProperties(api, {
    active: { get: function () { return running; } }, state: { get: function () { return state; } },
    tier: { get: function () { return LOW_END ? 'low' : 'std'; } }, wechat: { get: function () { return /MicroMessenger/i.test(UA); } },
    devices: { get: function () { return devices.slice(); } }, deviceId: { get: function () { return selectedDevice; } }
  });
  window.__CFTrackerMobile = api;
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot, { once: true });
  else boot();
})();
