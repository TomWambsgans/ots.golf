"""The record chart: each track's record as a step curve over time, rendered as inline SVG.

Two series only, fixed colors (lower = series 1, upper = series 2), 2px lines, markers with a
2px surface ring, direct labels at the right end plus a legend, recessive grid, and the point
list the page's hover script uses for the crosshair tooltip.
"""
from __future__ import annotations

import json
from datetime import datetime, timedelta
from html import escape

W, H = 960, 340
ML, MR, MT, MB = 48, 160, 30, 40
SERIES = {"lower": ("Lower bound", "s1"), "upper": ("Upper bound", "s2")}


def _nice_ticks(lo: float, hi: float) -> list[int]:
    span = max(hi - lo, 1)
    step = 5 if span <= 40 else 10 if span <= 100 else 20 if span <= 250 else 50
    start = int(lo // step) * step
    return [v for v in range(start, int(hi) + step, step) if lo <= v <= hi]


def _time_ticks(t0: datetime, t1: datetime, n: int = 5) -> list[datetime]:
    span = (t1 - t0).total_seconds()
    return [t0 + timedelta(seconds=span * i / (n - 1)) for i in range(n)]


def record_chart(curves: dict[str, list[dict]], baselines: dict[str, int], now: datetime,
                 literature: list[dict] | None = None) -> dict:
    """curves[slug]: ascending list of {t, claim, id, login}; literature: [{t, label, url, note, lower?, upper?}]."""
    literature = literature or []
    all_t = [p["t"] for pts in curves.values() for p in pts] + [p["t"] for p in literature]
    t1 = now
    t0 = min(all_t) if all_t else now - timedelta(days=7)
    if t1 - t0 < timedelta(days=7):
        t0 = t1 - timedelta(days=7)
    t0 = t0 - (t1 - t0) * 0.03
    claims = [p["claim"] for pts in curves.values() for p in pts] + list(baselines.values()) \
        + [p[k] for p in literature for k in ("lower", "upper") if p.get(k) is not None]
    y_lo, y_hi = max(min(claims) - 6, -1), max(claims) + 6
    y_lo, y_hi = int(y_lo // 5) * 5, int(-(-y_hi // 5)) * 5

    def sx(t: datetime) -> float:
        return ML + (W - ML - MR) * (t - t0).total_seconds() / max((t1 - t0).total_seconds(), 1)

    def sy(v: float) -> float:
        return MT + (H - MT - MB) * (y_hi - v) / max(y_hi - y_lo, 1)

    out = [f'<svg viewBox="0 0 {W} {H}" class="record-chart" role="img" '
           f'aria-label="Records over time: lower and upper bound in hash units">']
    # grid + y axis
    for v in _nice_ticks(y_lo, y_hi):
        y = sy(v)
        out.append(f'<line class="grid" x1="{ML}" x2="{W - MR}" y1="{y:.1f}" y2="{y:.1f}"/>')
        out.append(f'<text class="tick" x="{ML - 8}" y="{y + 4:.1f}" text-anchor="end">{v}</text>')
    # x axis
    out.append(f'<line class="axis" x1="{ML}" x2="{W - MR}" y1="{H - MB}" y2="{H - MB}"/>')
    for t in _time_ticks(t0, t1):
        x = sx(t)
        out.append(f'<text class="tick" x="{x:.1f}" y="{H - MB + 18}" text-anchor="middle">{t.strftime("%b %d")}</text>')
    out.append(f'<text class="tick" x="{ML - 8}" y="{MT - 14}" text-anchor="end">units</text>')

    points: list[dict] = []
    for slug, (label, cls) in SERIES.items():
        pts = curves.get(slug, [])          # verified records, ascending
        lits = [p for p in literature if p.get(slug) is not None]
        lits = sorted(lits, key=lambda p: p["t"])
        x_end = sx(t1)
        # reference points: hollow markers, dashed step, until the first verified record
        first_rec_x = sx(pts[0]["t"]) if pts else x_end
        if lits:
            d = f"M{sx(lits[0]['t']):.1f},{sy(lits[0][slug]):.1f}"
            for nxt in lits[1:]:
                d += f" H{sx(nxt['t']):.1f} V{sy(nxt[slug]):.1f}"
            d += f" H{first_rec_x:.1f}"
            if pts:
                d += f" V{sy(pts[0]['claim']):.1f}"
            out.append(f'<path class="line {cls} dashed" d="{d}"/>')
            for p in lits:
                x, y = sx(p["t"]), sy(p[slug])
                out.append(f'<circle class="mark hollow {cls}" cx="{x:.1f}" cy="{y:.1f}" r="4.5"/>')
                points.append({"x": round(x, 1), "y": round(y, 1), "track": label, "claim": p[slug],
                               "login": p["label"], "date": p["t"].strftime("%Y-%m-%d"), "id": None,
                               "url": p.get("url"), "note": p.get("note", "")})
        if not pts:
            y_last = sy(lits[-1][slug]) if lits else sy(baselines[slug])
            if not lits:
                out.append(f'<line class="line {cls} dashed" x1="{ML}" x2="{x_end:.1f}" y1="{y_last:.1f}" y2="{y_last:.1f}"/>')
            v_last = lits[-1][slug] if lits else baselines[slug]
            out.append(f'<text class="label {cls}" x="{x_end + 8:.1f}" y="{y_last + 4:.1f}">{label} {v_last}'
                       f'<tspan class="muted" x="{x_end + 8:.1f}" dy="15">paper, unverified</tspan></text>')
            continue
        d = f"M{sx(pts[0]['t']):.1f},{sy(pts[0]['claim']):.1f}"
        for prev, nxt in zip(pts, pts[1:]):
            d += f" H{sx(nxt['t']):.1f} V{sy(nxt['claim']):.1f}"
        d += f" H{x_end:.1f}"
        out.append(f'<path class="line {cls}" d="{d}"/>')
        for p in pts:
            x, y = sx(p["t"]), sy(p["claim"])
            out.append(f'<circle class="mark {cls}" cx="{x:.1f}" cy="{y:.1f}" r="4.5"/>')
            points.append({"x": round(x, 1), "y": round(y, 1), "track": label, "claim": p["claim"],
                           "login": p["login"], "date": p["t"].strftime("%Y-%m-%d %H:%M UTC"), "id": p["id"]})
        last = pts[-1]
        out.append(f'<text class="label {cls}" x="{x_end + 8:.1f}" y="{sy(last["claim"]) + 4:.1f}">'
                   f'{label} {last["claim"]}</text>')
    out.append('<line class="crosshair" x1="0" x2="0" y1="0" y2="0" visibility="hidden"/>')
    out.append("</svg>")
    return {"svg": "\n".join(out), "points": json.dumps(points), "y_range": (y_lo, y_hi)}


def esc(s: str) -> str:
    return escape(s, quote=True)
