// 银河铁道之夜 · camera-space body / head / eye response.
// After controls.update(): restore = __cfApplyTrackingView(camera, controls).
// Render the scene AND project its labels before restore() in a finally block.
// No CSS transforms, independent animation loop, or persistent controls mutation.
(function () {
  'use strict';
  if (window.__cfApplyTrackingView) return;
  window.__cfMotion = true;

  var lastTime = null, lastFrame = null, frameSeenAt = -Infinity;
  var yaw = 0, pitch = 0, roll = 0;
  var head = { center: null, started: 0, seen: -Infinity };
  var torso = { center: null, started: 0, seen: -Infinity };
  var pointers = new Set(), touches = 0;
  var pending = new WeakMap();
  var renderedCameras = new WeakMap();
  var noop = function () {};
  var reduced = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)');
  function clamp(x, max) { return Math.max(-max, Math.min(max, x)); }
  function valid(p) { return p && p.visible !== false && Number.isFinite(p.x) && Number.isFinite(p.y); }
  function sceneTarget(target) { return target && target.id === 'cv'; }
  document.addEventListener('pointerdown', function (event) {
    if (event.isTrusted && sceneTarget(event.target)) pointers.add(event.pointerId);
  }, true);
  function release(event) { pointers.delete(event.pointerId); }
  document.addEventListener('pointerup', release, true);
  document.addEventListener('pointercancel', release, true);
  document.addEventListener('touchstart', function (event) {
    if (event.isTrusted && sceneTarget(event.target)) touches = event.touches.length;
  }, { capture: true, passive: true });
  function releaseTouch(event) { touches = event.touches.length; }
  document.addEventListener('touchend', releaseTouch, { capture: true, passive: true });
  document.addEventListener('touchcancel', releaseTouch, { capture: true, passive: true });
  window.addEventListener('blur', function () { pointers.clear(); touches = 0; });

  // First 650 ms establish a resting center, then lock it so a lean is intentional.
  // A long absence resets calibration for the next viewer.
  function centered(point, state, now, dt) {
    if (!valid(point)) {
      if (now - state.seen > 2200) state.center = null;
      return { x: 0, y: 0, roll: 0 };
    }
    if (now - state.seen > 2200) state.center = null;
    state.seen = now;
    var pointRoll = Number.isFinite(point.roll) ? point.roll : 0;
    if (!state.center) {
      state.center = { x: point.x, y: point.y, roll: pointRoll };
      state.started = now;
    }
    if (now - state.started < 650) {
      var a = 1 - Math.exp(-dt / .22);
      state.center.x += (point.x - state.center.x) * a;
      state.center.y += (point.y - state.center.y) * a;
      state.center.roll += (pointRoll - state.center.roll) * a;
      return { x: 0, y: 0, roll: 0 };
    }
    return { x: clamp((point.x - state.center.x) * 2, 1),
      y: clamp((point.y - state.center.y) * 2, 1),
      roll: clamp(pointRoll - state.center.roll, .4) };
  }
  function navigationBusy(track, controls) {
    var hands = track && track.hands || [];
    return pointers.size > 0 || touches > 0 || hands.some(function (hand) { return hand && hand.pinch; }) ||
      !!(window.__cf01PinchZoomOn && window.__cf01PinchZoomOn()) ||
      !!(controls && controls.enabled === false) || !!(window.flyState || window.solarFly ||
      window.solarWarp || window.skyDive || window.skyArrival || window.solarScaleAnim || window.solarEventRide);
  }
  function smooth(controls) {
    var now = performance.now();
    var dt = lastTime === null ? 1 / 60 : Math.min(.1, Math.max(0, (now - lastTime) / 1000));
    lastTime = now;
    var track = window.__exhibitTrack;
    if (track !== lastFrame) { lastFrame = track; frameSeenAt = now; }
    var fresh = track && now - frameSeenAt < 1200 &&
      (!Number.isFinite(track.t) || Math.abs(Date.now() - track.t) < 1500);
    var h = centered(fresh ? track.face : null, head, now, dt);
    var b = centered(fresh ? track.body : null, torso, now, dt);
    var eyes = fresh && valid(track.face) && track.eyes;
    var gx = eyes && Number.isFinite(eyes.gx) ? clamp(eyes.gx, 1) : 0;
    var gy = eyes && Number.isFinite(eyes.gy) ? clamp(eyes.gy, 1) : 0;
    var busy = navigationBusy(fresh ? track : null, controls);
    var gain = reduced && reduced.matches ? .35 : 1;
    var targetYaw = busy ? 0 : clamp(h.x * .11 + b.x * .055 + gx * .075, .18) * gain;
    var targetPitch = busy ? 0 : clamp(h.y * .085 + b.y * .04 + gy * .055, .13) * gain;
    var targetRoll = busy ? 0 : clamp(h.roll * .09, .025) * gain;
    var a = 1 - Math.exp(-dt / (busy ? .24 : .16));
    yaw += (targetYaw - yaw) * a;
    pitch += (targetPitch - pitch) * a;
    roll += (targetRoll - roll) * a;
  }

  function rememberRendered(camera) {
    var snapshot = renderedCameras.get(camera);
    if (!snapshot) { snapshot = camera.clone(false); renderedCameras.set(camera, snapshot); }
    else snapshot.copy(camera, false);
    // copy() preserves world/projection matrices; these are the exact matrices used
    // by the renderer, including any parent transform, rather than a second update.
  }
  window.__cfTrackedCamera = function (camera) { return renderedCameras.get(camera) || camera; };

  window.__cfApplyTrackingView = function (camera, controls) {
    var THREE = window.THREE;
    if (!camera || !THREE) return noop;
    // A forgotten restore must not accumulate displacement on the next frame.
    var previous = pending.get(camera);
    if (previous) previous();
    smooth(controls);
    if (Math.abs(yaw) + Math.abs(pitch) + Math.abs(roll) < .00001) {
      camera.updateMatrixWorld(true);
      rememberRendered(camera);
      return noop;
    }
    var position = camera.position.clone(), quaternion = camera.quaternion.clone(), up = camera.up.clone();
    var target = controls && controls.target;
    if (target && THREE.Spherical) {
      var offset = position.clone().sub(target);
      if (offset.lengthSq() > 1e-10) {
        var spherical = new THREE.Spherical().setFromVector3(offset);
        spherical.theta -= yaw;
        spherical.phi = Math.max(.025, Math.min(Math.PI - .025, spherical.phi - pitch));
        camera.position.copy(target).add(offset.setFromSpherical(spherical));
        camera.lookAt(target);
      } else { camera.rotateY(-yaw); camera.rotateX(pitch); }
    } else { camera.rotateY(-yaw); camera.rotateX(pitch); }
    if (roll) camera.rotateZ(-roll);
    camera.updateMatrixWorld(true);
    rememberRendered(camera);
    var restored = false;
    function restore() {
      if (restored) return;
      restored = true;
      camera.position.copy(position); camera.quaternion.copy(quaternion); camera.up.copy(up);
      camera.updateMatrixWorld(true);
      if (pending.get(camera) === restore) pending.delete(camera);
    }
    pending.set(camera, restore);
    return restore;
  };
})();
