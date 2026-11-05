(function () {
  'use strict';
  var button = document.getElementById('artwork-fullscreen');
  if (!document.fullscreenEnabled && !document.documentElement.webkitRequestFullscreen) button.hidden = true;
  button.addEventListener('click', async function () {
    try {
      if (document.fullscreenElement) await document.exitFullscreen();
      else if (document.documentElement.requestFullscreen) await document.documentElement.requestFullscreen();
      else document.documentElement.webkitRequestFullscreen();
    } catch (error) { console.warn('Fullscreen unavailable:', error.name); }
  });
  document.addEventListener('fullscreenchange', function () {
    var label = document.fullscreenElement ? 'Exit fullscreen' : 'Fullscreen';
    button.setAttribute('aria-label', label);
    button.title = label;
  });
  setInterval(function () { document.body.dataset.view = window.viewMode || 'galaxy'; }, 100);
  document.getElementById('audiobtn').title = 'Music';
  document.getElementById('audiobtn').setAttribute('aria-label', 'Toggle music');
})();
