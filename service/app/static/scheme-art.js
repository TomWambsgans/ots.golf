(function () {
  // A fresh random signature in the iris at load, and another one every two seconds: a uniform
  // element of the scheme's disclosure family (Cuts.lean), the cuts of cost 105 with at most 41
  // revealed values, of three shapes (revealed subtrees, revealed groups, chain cost). The shape is
  // drawn by its share of the family, the digests uniformly, and the chain positions exactly
  // through the counting table (doubles carry the ratios).
  var svg = document.querySelector('svg.scheme-art');
  if (!svg) return;
  var LEN = +svg.dataset.len, SUBTREES = 7, GROUPS = 21, CHAINS = 63;
  var SHAPES = svg.dataset.shapes.split(';').map(function (t) { return t.split(',').map(Number); });
  var els = Array.prototype.slice.call(svg.querySelectorAll('[data-r]'));
  var TOP = Math.max.apply(null, SHAPES.map(function (t) { return t[2]; }));
  var ways = [[]], n, s, c;                        // ways[n][s]: s hashes on n chains, each 0..LEN
  for (s = 0; s <= TOP; s++) ways[0].push(s === 0 ? 1 : 0);
  for (n = 1; n <= CHAINS; n++) { ways.push([]); for (s = 0; s <= TOP; s++) {
    var acc = 0; for (c = 0; c <= Math.min(LEN, s); c++) acc += ways[n - 1][s - c]; ways[n].push(acc); } }
  function choose(m, k) { var r = 1; for (var i = 1; i <= k; i++) r = r * (m - k + i) / i; return r; }
  var weights = SHAPES.map(function (t) { return choose(SUBTREES, t[0]) * choose(GROUPS - 3 * t[0], t[1]) * ways[CHAINS - 9 * t[0] - 3 * t[1]][t[2]]; });
  var total = weights.reduce(function (x, y) { return x + y; }, 0);
  function pick(list, k) {                         // k distinct elements, uniformly
    var pool = list.slice(), out = [];
    for (var i = 0; i < k; i++) out.push(pool.splice(Math.floor(Math.random() * pool.length), 1)[0]);
    return out;
  }
  function sample() {
    var r = Math.random() * total, shape = SHAPES[SHAPES.length - 1], i, j, k;
    for (i = 0; i < SHAPES.length; i++) { if (r < weights[i]) { shape = SHAPES[i]; break; } r -= weights[i]; }
    var all = []; for (i = 0; i < SUBTREES; i++) all.push(i);
    var revE = {}; pick(all, shape[0]).forEach(function (l) { revE[l] = true; });
    var under = []; for (j = 0; j < GROUPS; j++) if (!revE[Math.floor(j / 3)]) under.push(j);
    var revG = {}; pick(under, shape[1]).forEach(function (g) { revG[g] = true; });
    var chains = []; for (k = 0; k < CHAINS; k++) { j = Math.floor(k / 3); if (!revE[Math.floor(j / 3)] && !revG[j]) chains.push(k); }
    var t = {}, budget = shape[2];
    chains.forEach(function (k, idx) {
      var left = chains.length - idx, x = Math.random() * ways[left][budget], c = 0;
      while (c < Math.min(LEN, budget) && x >= ways[left - 1][budget - c]) { x -= ways[left - 1][budget - c]; c++; }
      t[k] = LEN - c; budget -= c;
    });
    return { revE: revE, revG: revG, t: t };
  }
  function set(el, c) { var cl = el.classList; if (!cl.contains(c)) { cl.remove('revealed', 'recomputed', 'untouched'); cl.add(c); } }
  function light(cut) {
    els.forEach(function (el) {
      var d = el.dataset, k, tk, j;
      if (d.r === 'bead' || d.r === 'cedge') {
        k = +d.k; tk = cut.t[k];
        if (tk === undefined) return set(el, 'untouched');
        if (d.r === 'bead') return set(el, +d.t === tk ? 'revealed' : +d.t > tk ? 'recomputed' : 'untouched');
        return set(el, +d.t > tk ? 'recomputed' : 'untouched');
      }
      if (d.r === 'g' || d.r === 'tip') {
        j = +d.g;
        var hidden = cut.revE[Math.floor(j / 3)];
        if (d.r === 'g') return set(el, hidden ? 'untouched' : cut.revG[j] ? 'revealed' : 'recomputed');
        return set(el, hidden || cut.revG[j] ? 'untouched' : 'recomputed');
      }
      if (d.r === 's') return set(el, cut.revE[+d.s] ? 'revealed' : 'recomputed');
      if (d.r === 'gedge') return set(el, cut.revE[+d.s] ? 'untouched' : 'recomputed');
    });
  }
  light(sample());
  var motion = window.matchMedia('(prefers-reduced-motion: reduce)');
  var aperture = svg.querySelector('[data-eye-aperture]');
  var upperLid = svg.querySelector('.lid-upper'), lowerLid = svg.querySelector('.lid-lower');
  var patternTimer, blinkTimer, frame;
  function openEye(amount) {
    var top = 280 - 310 * amount, bottom = 280 + 310 * amount;
    var upper = 'M 22 280 C 196 ' + top + ' 664 ' + top + ' 838 280';
    var lower = 'M 838 280 C 664 ' + bottom + ' 196 ' + bottom + ' 22 280';
    aperture.setAttribute('d', upper + ' ' + lower + ' Z');
    upperLid.setAttribute('d', upper); lowerLid.setAttribute('d', lower);
  }
  function blink() {
    var start;
    function tick(now) {
      if (start === undefined) start = now;
      var elapsed = now - start;
      // Close briskly, hold for an instant, then reopen gently. The iris stays still.
      var amount = elapsed < 110 ? 1 - elapsed / 110 : elapsed < 150 ? 0 : Math.min(1, (elapsed - 150) / 190);
      openEye(amount * amount * (3 - 2 * amount));
      frame = elapsed < 340 ? requestAnimationFrame(tick) : undefined;
    }
    frame = requestAnimationFrame(tick);
  }
  function updateMotion() {
    clearInterval(patternTimer); clearInterval(blinkTimer); cancelAnimationFrame(frame);
    if (aperture) openEye(1);
    if (motion.matches || document.hidden) return;
    patternTimer = setInterval(function () { light(sample()); }, 2000);
    if (aperture) blinkTimer = setInterval(blink, 10000);
  }
  motion.addEventListener('change', updateMotion);
  document.addEventListener('visibilitychange', updateMotion);
  updateMotion();
})();
