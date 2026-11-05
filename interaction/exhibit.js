// ============================================================
// 银河铁道之夜 · local camera edition, based on 07-camera-interaction/exhibit.js v4.
// In-page frame events replace WebSocket/polling; 01 navigation targets its canvas.
// Combination transitions end before starting, and continuous zoom excludes fists.
// Pose visibility guards keep empty body frames out of synthetic pointer input.
// ============================================================
// ============================================================
// exhibit.js v4 — 身体引力场 · 统一适配层（注入各视觉页 </body> 前）
// 用法: <script src="http://localhost:9100/exhibit.js" data-id="03" data-cn="星尘引力"
//      data-en="STELLAR GRAVITY" data-hint="张开双手缩放宇宙"></script>
// 功能: a) 统一展项标版（共场 COMMON FIELD） b) 隐藏原项目出处/UI
//    c) 手势→合成输入事件 d) exhibit:* CustomEvent
//    e) window.__exhibitTrack（原样透传 tracker 全字段, 含 v3 的 hand/gesture/gscore/fingers/vel 与 v4 的 eyes/combo）
//     + window.__exhibitGestures（最近 5 个已触发手势 {name,t} 队列）
//     + window.__exhibitGaze（{gx,gy} 最新平滑视线值, 归一化 [-1,1]）
//    f) WS 地址随 script src 智能推导 g) 断线重连
// CustomEvent（全部 bubbles:true，挂 document.body 派发）:
//  exhibit:pinch-start / exhibit:pinch-end detail:{x,y,px,py}  x,y=归一化镜像坐标, px,py=视口像素
//  exhibit:fist    detail:{x,y,px,py,id}（任一手 fist false→true 派发一次）
//  exhibit:fist-end  （全部手不再 fist 时派发一次）
//  exhibit:wave    detail:{id,px,py}（同时合成 Space keydown/keyup）
//  exhibit:spread   detail:{delta,spread,px,py}（双手张合变化超阈值, delta=本次变化量）
//  exhibit:gesture   detail:{name,score,x,y,px,py,hand}（tracker v3 稳定手势: 主手 hands[0]
//            官方类别 Closed_Fist/Open_Palm/Pointing_Up/Thumb_Down/Thumb_Up/Victory/ILoveYou
//            类别变化且非 null、gscore≥0.6、连续帧稳定 ≥250ms 去抖后派发一次;
//            切回 null/低分/手消失 不派发仅重置, 中断后同类别再进入可再次触发;
//            hand="Left"/"Right"）。触发时右下角 hint 上方短暂显示手势名 1.5s 渐隐
//  exhibit:combo  detail:{name,x,y,px,py}（tracker v4 顶层 combo 双手组合: 由 null→非空或
//            A→B 切换时派发一次; name=double-fist/double-palm/double-pinch/fist-palm;
//            x,y=双手中点归一化, px,py=视口像素, 取不到双手位置时为视口中心;
//            触发时右下角短暂显示中文名「双手握拳/双手张开/双手捏合/拳张切换」1.5s 渐隐）
//  exhibit:combo-end detail:{name}（combo 由非空→null 时派发一次, name=刚结束的组合）
//  exhibit:gaze  detail:{gx,gy}（tracker v4 顶层 eyes.gx/gy 归一化 [-1,1]; 原始值偏离已
//            接受目标超死区 0.06 才接受新目标, 输出 EMA 0.5 平滑, 有变化时节流 8Hz 派发;
//            window.__exhibitGaze 同步最新平滑值）
// ============================================================
(function () {
 'use strict';
 var script = document.currentScript;
 var EXHIBIT_ID = (script && script.dataset.id) || '00';
 var EXHIBIT_CN = (script && script.dataset.cn) || '';
 var EXHIBIT_EN = (script && script.dataset.en) || '';
 var EXHIBIT_HINT = (script && script.dataset.hint) || ''; // 未设置则不显示
 var RECONNECT_MS = 3000;
 var SPREAD_TO_WHEEL = -800; // 双手张合 → wheel 的增益（拉开=放大，deltaY 为负）
 var SPREAD_THRESHOLD = 0.003;
 var GESTURE_MIN_SCORE = 0.6; // 稳定手势触发分数下限（tracker v3 hands[].gscore）
 var GESTURE_STABLE_MS = 140; // 同类别连续帧稳定时长（去抖; 2026-09-13 由 250 降至 140 提速响应）
 var GESTURE_FLASH_MS = 1500; // 手势名在右下角 hint 上方的停留时长
 var GESTURE_EMOJI = { // 官方类别 → 中文别名（无 emoji，纯文字）
  Closed_Fist: '握拳', Open_Palm: '手掌', Pointing_Up: '单指',
  Thumb_Down: '点踩', Thumb_Up: '点赞', Victory: 'V手势', ILoveYou: '爱之手'
 };
 var COMBO_CN = { // tracker v4 combo → 中文名（gestureFlash 用, 白色纯文字无 emoji）
  'double-fist': '双手握拳', 'double-palm': '双手张开',
  'double-pinch': '双手捏合', 'fist-palm': '拳张切换'
 };
 var GAZE_DEADZONE = 0.06; // 原始视线偏离已接受目标超过该值才接受更新（死区）
 var GAZE_EMA = 0.5;    // 平滑输出向已接受目标的指数移动平均系数
 var GAZE_MIN_INTERVAL = 80; // exhibit:gaze 最小派发间隔 ms（12Hz 节流; 原为 125/8Hz）

 // ── WS 地址智能推导: 优先用本 script 标签 src 的 host（跨机加载 http://100.x.x.x:9100/exhibit.js
 //  时 ws 连同一 host），取不到再兜底 ws://localhost:9100 ──
 var WS_URL = 'ws://localhost:9100';
 try {
  if (script && script.src) {
   var su = new URL(script.src, location.href);
   if (su.protocol === 'http:' || su.protocol === 'https:') {
    WS_URL = (su.protocol === 'https:' ? 'wss:' : 'ws:') + '//' + su.host;
   }
  }
 } catch (e) { /* 保持兜底地址 */ }

 // 最近一帧 track payload（全页面可读，随 tracker ~16Hz 更新；tracker v3 新增字段原样透传）
 window.__exhibitTrack = null;
 // 最近 5 个已触发的稳定手势 {name, t}（t=Date.now()，调试/展项用）
 window.__exhibitGestures = [];
 // 最新平滑视线值 {gx, gy}（归一化 [-1,1]，随 gaze 管道同步更新，无 eyes 时保持上次值）
 window.__exhibitGaze = { gx: 0, gy: 0 };

 // ── a) 统一展项标版 ──
 var css = document.createElement('style');
 css.textContent =
  '#exhibit-badge{position:fixed;top:12px;left:14px;z-index:999999;pointer-events:none;' +
  'font:12px/1.6 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.18em;' +
  'color:rgba(255,255,255,.85);background:rgba(0,0,0,.55);border:1px solid rgba(255,255,255,.14);' +
  'border-radius:8px;padding:6px 12px;}' +
  '#exhibit-badge .exhibit-brand{font-size:10px;letter-spacing:.3em;color:rgba(255,255,255,.55);}' +
  '#exhibit-badge .exhibit-name{font-size:13px;letter-spacing:.14em;color:rgba(255,255,255,.92);margin-top:2px;}' +
  '#exhibit-gravity{position:fixed;bottom:10px;right:14px;z-index:999999;pointer-events:none;text-align:right;' +
  'font:11px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;letter-spacing:.14em;' +
  'color:rgba(255,255,255,.30);transition:color .3s,text-shadow .3s;}' +
  '#exhibit-gravity .exhibit-hint{font-size:10px;opacity:.55;letter-spacing:.08em;margin-top:2px;}' +
  '#exhibit-gravity .exhibit-gesture{font-size:13px;letter-spacing:.1em;margin-top:2px;' +
  'color:rgba(255,255,255,.95);text-shadow:0 0 8px rgba(255,255,255,.45);' +
  'opacity:0;transform:translateY(4px);transition:opacity .35s,transform .35s;}' +
  '#exhibit-gravity .exhibit-gesture.show{opacity:1;transform:none;}' +
  '#exhibit-gravity.live{color:rgba(255,255,255,.95);text-shadow:0 0 10px rgba(255,255,255,.6);}';
 // ── b) 按展项隐藏原项目出处/控制面板/说明层（选择器已对照各项目源码确认）──
 var HIDE = {
  '01': '#lang,#title,#solarstrip,#galaxystrip', // galaxy-explorer: 语言切换/原标题/底部导航条
  '02': '.link-bar,.dg,#hint-text',       // black-hole: 底部链接栏/dat.gui/提示文字
  '03': '.tp-dfwv,#info',            // webgpu-galaxy: Tweakpane 面板/左上角 HUD
  '04': '.dg,.promo',              // WebGL-Fluid: dat.gui 面板/推广弹窗
  '05': '',                   // n_body: 各页自行处理
  '06': '',                   // butterchurn-demo: 保留启动遮罩与预设名 HUD
  '07': '#help',                 // hydra-offline: 说明面板
  '08': '', '09': '', '10': '', '11': '', '12': '', '13': '', '14': '', '15': '' // 08-15: 各页自行处理
 };
 if (HIDE[EXHIBIT_ID]) css.textContent += HIDE[EXHIBIT_ID] + '{display:none!important;}';
 document.head.appendChild(css);

 // 左上角徽章: 两行 —— 「共场 COMMON FIELD」 / 「NN 中文名 EN-NAME」
 var badge = document.createElement('div');
 badge.id = 'exhibit-badge';
 var brand = document.createElement('div');
 brand.className = 'exhibit-brand';
 brand.textContent = '共场 COMMON FIELD';
 var nameLine = document.createElement('div');
 nameLine.className = 'exhibit-name';
 nameLine.textContent = [EXHIBIT_ID, EXHIBIT_CN, EXHIBIT_EN].filter(Boolean).join(' ');
 badge.appendChild(brand);
 badge.appendChild(nameLine);
 document.body.appendChild(badge);

 // 右下角两行: 「身体即引力 BODY AS GRAVITY」 + data-hint（更小字号/更低透明度, 未设置则不显示）
 // exhibit:gesture 触发时, hint 文本上方短暂显示手势名（如「V手势 Victory」）1.5s 后纯 CSS 渐隐
 var gravity = document.createElement('div');
 gravity.id = 'exhibit-gravity';
 var gravityMain = document.createElement('div');
 gravityMain.textContent = '身体即引力 BODY AS GRAVITY';
 gravity.appendChild(gravityMain);
 var gestureFlash = document.createElement('div');
 gestureFlash.className = 'exhibit-gesture';
 if (EXHIBIT_HINT) {
  var gravityHint = document.createElement('div');
  gravityHint.className = 'exhibit-hint';
  gravityHint.textContent = EXHIBIT_HINT;
  gravity.appendChild(gestureFlash);
  gravity.appendChild(gravityHint);
 } else {
  gravity.appendChild(gestureFlash);
 }
 document.body.appendChild(gravity);

 var gestureFlashTimer = 0;
 function flashGestureText(text) { // 停留 1.5s 后移除 .show → CSS 渐隐, 不阻塞
  gestureFlash.textContent = text;
  gestureFlash.classList.add('show');
  if (gestureFlashTimer) clearTimeout(gestureFlashTimer);
  gestureFlashTimer = setTimeout(function () {
   gestureFlash.classList.remove('show');
   gestureFlashTimer = 0;
  }, GESTURE_FLASH_MS);
 }
 function showGestureFlash(name) {
  flashGestureText((GESTURE_EMOJI[name] || '手势') + ' ' + name);
 }
 function showComboFlash(name) { // combo 触发同样在右下角闪现中文名（白色文字, 无 emoji）
  flashGestureText((COMBO_CN[name] || '双手手势') + ' ' + name);
 }

 // ── c) 手势 → 合成输入事件 + exhibit:* CustomEvent ──
 var dragging = false;    // pinch 拖拽中
 var lastX = -1, lastY = -1; // 上次派发的像素坐标（去重）
 var prevSpread = null;   // 上一帧双手间距
 var lastDrift = 0;     // body 漂移上次派发时间
 var lastActive = 0;     // 最近一次有手可见的时间（驱动右下角高亮）
 var fistState = {};     // id → 上一帧是否握拳（检测 fist 上升沿）
 var prevAnyFist = false;  // 上一帧是否存在握拳的手（检测 fist-end 下降沿）
 var gestCand = null;    // 主手当前候选手势类别（连续帧缓存; null=无/低分/无手）
 var gestSince = 0;     // 候选类别开始时刻（performance.now）
 var gestFired = false;   // 本轮候选是否已派发（防每帧重复派发）
 var prevCombo = null;   // 上一帧 combo（null=无; 检测 null→非空 / A→B / 非空→null 沿）
 var gazeTargetX = 0, gazeTargetY = 0; // 死区判定后已接受的原始注视目标
 var gazeX = 0, gazeY = 0;       // EMA 平滑后的注视输出（同步到 __exhibitGaze）
 var gazeLastEmit = -1e3;    // exhibit:gaze 上次派发时刻（节流用; 负值让首帧立即可发）

 function pointTarget(cx, cy) {
  // Camera gestures navigate the artwork even when their position overlaps its PiP or cards.
  if (EXHIBIT_ID === '01') return document.getElementById('cv') || document.body;
  return document.elementFromPoint(cx, cy) || document.body;
 }
 // 在 document.body 上派发 exhibit:* CustomEvent（全部 bubbles:true）
 function emit(name, detail) {
  var target = document.body || document.documentElement;
  try { target.dispatchEvent(new CustomEvent(name, { bubbles: true, detail: detail })); } catch (e) {}
 }
 // 派发一组 pointer+mouse 事件；type 形如 'down'/'move'/'up'
 function firePointerMouse(kind, cx, cy) {
  var target = pointTarget(cx, cy);
  var pressed = kind !== 'up' && dragging;
  var base = {
   bubbles: true, cancelable: true, view: window,
   clientX: cx, clientY: cy, screenX: cx, screenY: cy,
   button: 0, buttons: kind === 'up' ? 0 : (pressed ? 1 : 0)
  };
  var init = Object.assign({ pointerType: 'mouse', isPrimary: true, pointerId: 1 }, base);
  var pe = (typeof PointerEvent === 'function')
   ? new PointerEvent('pointer' + kind, init)
   : new MouseEvent('mouse' + kind, base);
  target.dispatchEvent(pe);
  target.dispatchEvent(new MouseEvent('mouse' + kind, base));
 }

 function fireWheel(cx, cy, deltaY) {
  var target = pointTarget(cx, cy);
  target.dispatchEvent(new WheelEvent('wheel', {
   bubbles: true, cancelable: true, view: window,
   clientX: cx, clientY: cy, deltaY: deltaY, deltaMode: 0
  }));
 }

 function fireWave(px, py) {
  var target = document.body || document.documentElement;
  var init = { key: ' ', code: 'Space', keyCode: 32, which: 32, bubbles: true, cancelable: true, view: window };
  target.dispatchEvent(new KeyboardEvent('keydown', init)); // butterchurn 换预设 / 游戏射击
  target.dispatchEvent(new KeyboardEvent('keyup', init));
  emit('exhibit:wave', { id: EXHIBIT_ID, px: px, py: py });
 }

 function handleTrack(p) {
  var vw = window.innerWidth, vh = window.innerHeight;
  var hands = p.hands || [];
  var i, h, k;

  // 握拳: 任一手 fist false→true 上升沿派发一次; 全部手不再 fist 时派发一次 fist-end
  var anyFist = false;
  var seenIds = {};
  for (i = 0; i < hands.length; i++) {
   h = hands[i];
   if (!h || typeof h.x !== 'number' || typeof h.y !== 'number') continue;
   var hid = String(h.id);
   seenIds[hid] = true;
   var isFist = !!h.fist;
   if (isFist) {
    anyFist = true;
    if (!fistState[hid]) {
     emit('exhibit:fist', {
      x: h.x, y: h.y,
      px: Math.round(h.x * vw), py: Math.round(h.y * vh),
      id: h.id
     });
    }
   }
   fistState[hid] = isFist;
  }
  for (k in fistState) { if (!seenIds[k]) delete fistState[k]; } // 清理已消失的手
  if (prevAnyFist && !anyFist) emit('exhibit:fist-end');
  prevAnyFist = anyFist;

  // 稳定手势: 主手(hands[0])类别变化且非 null、gscore≥0.6、连续帧稳定 ≥250ms 去抖后派发一次。
  // 切回 null（类别为空/低分/无手）只重置不派发; 中断后同类别再进入算新一轮, 可再次触发。
  var mh = hands[0] || null;
  var gest = (mh && typeof mh.x === 'number' && typeof mh.y === 'number' &&
        typeof mh.gesture === 'string' && mh.gesture &&
        typeof mh.gscore === 'number' && mh.gscore >= GESTURE_MIN_SCORE)
        ? mh.gesture : null;
  var nowMs = performance.now();
  if (gest !== gestCand) { // 类别变化（含 →null）: 重置计时, 不派发
   gestCand = gest;
   gestSince = nowMs;
   gestFired = false;
  } else if (!gestFired && gest && nowMs - gestSince >= GESTURE_STABLE_MS) {
   gestFired = true; // 本轮只派发一次
   emit('exhibit:gesture', {
    name: gest,
    score: mh.gscore,
    x: mh.x, y: mh.y,
    px: Math.round(mh.x * vw), py: Math.round(mh.y * vh),
    hand: mh.hand || null
   });
   window.__exhibitGestures.push({ name: gest, t: Date.now() });
   if (window.__exhibitGestures.length > 5) window.__exhibitGestures.shift(); // 保留最近 5 个
   showGestureFlash(gest);
  }

  // End the previous combination before starting the next; nextName distinguishes release from change.
  var combo = (typeof p.combo === 'string' && p.combo) ? p.combo : null;
  if (combo !== prevCombo) {
   if (prevCombo) emit('exhibit:combo-end', { name: prevCombo, nextName: combo });
   if (combo) {
    var cbx = 0.5, cby = 0.5; // 取不到有效双手位置时 → 视口中心
    var ch0 = hands[0], ch1 = hands[1];
    if (ch0 && ch1 && typeof ch0.x === 'number' && typeof ch0.y === 'number' &&
        typeof ch1.x === 'number' && typeof ch1.y === 'number') {
     cbx = (ch0.x + ch1.x) / 2; // 双手中点（归一化）
     cby = (ch0.y + ch1.y) / 2;
    }
    emit('exhibit:combo', {
     name: combo,
     x: cbx, y: cby,
     px: Math.round(cbx * vw), py: Math.round(cby * vh)
    });
    showComboFlash(combo);
   }
   prevCombo = combo;
  }

  // 视线（tracker v4 顶层 eyes.gx/gy, 归一化 [-1,1]）: 原始值偏离已接受目标超死区 0.06 才
  // 接受新目标; 输出每帧向已接受目标 EMA(0.5) 收敛（静止注视也能收敛到位）;
  // 值有变化且距上次派发 ≥125ms 才发 exhibit:gaze（8Hz 节流）。__exhibitGaze 每帧同步。
  if (p.eyes && typeof p.eyes.gx === 'number' && typeof p.eyes.gy === 'number') {
   var grx = Math.max(-1, Math.min(1, p.eyes.gx));
   var gry = Math.max(-1, Math.min(1, p.eyes.gy));
   var gzMoved = false;
   if (Math.abs(grx - gazeTargetX) > GAZE_DEADZONE) { gazeTargetX = grx; gzMoved = true; }
   if (Math.abs(gry - gazeTargetY) > GAZE_DEADZONE) { gazeTargetY = gry; gzMoved = true; }
   var gpx = gazeX, gpy = gazeY;
   gazeX += (gazeTargetX - gazeX) * GAZE_EMA;
   gazeY += (gazeTargetY - gazeY) * GAZE_EMA;
   window.__exhibitGaze.gx = gazeX;
   window.__exhibitGaze.gy = gazeY;
   if ((gzMoved || Math.abs(gazeX - gpx) > 0.001 || Math.abs(gazeY - gpy) > 0.001) &&
       nowMs - gazeLastEmit >= GAZE_MIN_INTERVAL) {
    gazeLastEmit = nowMs;
    emit('exhibit:gaze', { gx: gazeX, gy: gazeY });
   }
  }

  if (hands.length > 0) {
   lastActive = performance.now();
   h = hands[0];
   var cx = Math.round(h.x * vw), cy = Math.round(h.y * vh);

   if (h.pinch && !dragging) {     // pinch 开始 → 按下
    dragging = true;
    firePointerMouse('down', cx, cy);
    emit('exhibit:pinch-start', { x: h.x, y: h.y, px: cx, py: cy });
   } else if (!h.pinch && dragging) {  // pinch 结束 → 抬起
    dragging = false;
    firePointerMouse('up', cx, cy);
    emit('exhibit:pinch-end', { x: h.x, y: h.y, px: cx, py: cy });
   }
   if (Math.abs(cx - lastX) >= 1 || Math.abs(cy - lastY) >= 1) { // 移动（拖拽中 buttons=1）
    firePointerMouse('move', cx, cy);
    lastX = cx; lastY = cy;
   }

   // Only two open palms or two pinches own continuous zoom; fist combinations never zoom.
   function openPalm(hand) {
    var fingers = hand && hand.fingers;
    return !!(hand && !hand.fist && !hand.pinch &&
      (hand.gesture === 'Open_Palm' || (fingers && fingers[1] && fingers[2] && fingers[3] && fingers[4])));
   }
   var pair = hands.length === 2 && hands[0] && hands[1];
   var pinchPair = pair && !hands[0].fist && !hands[1].fist && hands[0].pinch && hands[1].pinch;
   var zoomPair = pair && (pinchPair || (openPalm(hands[0]) && openPalm(hands[1])));
   if (zoomPair && Number.isFinite(p.handsSpread)) {
    if (prevSpread !== null) {
     var d = p.handsSpread - prevSpread;
     if (Math.abs(d) > SPREAD_THRESHOLD) {
      fireWheel(cx, cy, d * SPREAD_TO_WHEEL);
      var midX = Math.round((hands[0].x + hands[1].x) / 2 * vw);
      var midY = Math.round((hands[0].y + hands[1].y) / 2 * vh);
      emit('exhibit:spread', { delta: d, spread: p.handsSpread, px: midX, py: midY });
     }
    }
    prevSpread = p.handsSpread;
   } else {
    prevSpread = null;
   }
  } else {
   if (dragging) { // 手消失时补抬起
    dragging = false;
    var ux = lastX >= 0 ? lastX : Math.round(vw / 2);
    var uy = lastY >= 0 ? lastY : Math.round(vh / 2);
    firePointerMouse('up', ux, uy);
    emit('exhibit:pinch-end', { x: ux / vw, y: uy / vh, px: ux, py: uy });
   }
   prevSpread = null;
   // 无手可见时：body.x 缓慢变化 → 低频小幅 mousemove（视差漂移，4Hz）
   // 移动端 solo 模式：tracker-mobile 不跑 Pose 时 body 恒为 {visible:false}（无 x/y），
   // 加 visible!==false 守卫防止 p.body.x=undefined 产生 NaN mousemove 空转；
   // 桌面 WS 帧 body 为 {x,y} 或 null（无 visible 字段），行为完全不变。
   if (p.body && p.body.visible !== false && performance.now() - lastDrift > 250) {
    lastDrift = performance.now();
    var bx = Math.round(p.body.x * vw), by = Math.round(p.body.y * vh);
    firePointerMouse('move', bx, by);
   }
  }

  // 挥手: px,py 取主手位置（无手时取视口中心）
  if (p.wave) {
   var wpx = Math.round(vw / 2), wpy = Math.round(vh / 2);
   if (hands.length && typeof hands[0].x === 'number' && typeof hands[0].y === 'number') {
    wpx = Math.round(hands[0].x * vw);
    wpy = Math.round(hands[0].y * vh);
   }
   fireWave(wpx, wpy);
  }
 }

 // 右下角标签：手势激活时变亮
 setInterval(function () {
  gravity.classList.toggle('live', performance.now() - lastActive < 600);
 }, 200);

 // ── d) WebSocket 订阅（断线每 3 秒重连）──
 function connect() {
  var ws;
  try { ws = new WebSocket(WS_URL); } catch (e) { setTimeout(connect, RECONNECT_MS); return; }
  ws.onopen = function () { ws.send(JSON.stringify({ role: 'subscriber' })); };
  ws.onmessage = function (ev) {
   try {
    var p = JSON.parse(ev.data);
    if (p.type === 'track') { window.__exhibitTrack = p; handleTrack(p); }
   } catch (e) { /* 忽略坏包 */ }
  };
  ws.onclose = function () { setTimeout(connect, RECONNECT_MS); };
  ws.onerror = function () { try { ws.close(); } catch (e) {} };
 }
 // Consume in-page camera events immediately, deduplicating the initial snapshot by reference.
 (function boot() {
  var lastRef = null;
  function consume(f) {
   if (!f || f === lastRef || f.type !== 'track') return;
   lastRef = f;
   window.__exhibitTrack = f;
   handleTrack(f);
  }
  document.addEventListener('exhibit:solo-frame', function (event) { consume(event.detail); });
  consume(window.__cfSoloFrame);
 })();
})();
