(function () {
  function openTarget() {
    var target;
    try { target = decodeURIComponent(location.hash.slice(1)); } catch (error) { return; }
    var el = document.getElementById(target);
    while (el && el.tagName !== 'DETAILS') el = el.parentElement;
    if (el) { el.open = true; el.scrollIntoView(); }
  }
  window.addEventListener('hashchange', openTarget);
  openTarget();
})();
