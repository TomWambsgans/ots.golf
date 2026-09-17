"""Record history across scheme classes; an uncertified series stays off the numeric axis."""
from __future__ import annotations

import json
from datetime import datetime, timedelta
from html import escape

W, H = 960, 410
ML, MR, MT, MB = 48, 235, 30, 100


def _nice_ticks(lo: float, hi: float) -> list[int]:
    span = max(hi - lo, 1)
    step = 5 if span <= 40 else 10 if span <= 100 else 20 if span <= 250 else 50
    start = int(lo // step) * step
    return [v for v in range(start, int(hi) + step, step) if lo <= v <= hi]


def _time_ticks(t0: datetime, t1: datetime, n: int = 5) -> list[datetime]:
    span = (t1 - t0).total_seconds()
    return [t0 + timedelta(seconds=span * i / (n - 1)) for i in range(n)]


def record_chart(series: list[dict], now: datetime) -> dict:
    """Each series carries its own framework, kind, baseline (None if pending) and records."""
    numeric = [s for s in series if s["baseline"] is not None]
    pending = [s for s in series if s["baseline"] is None]
    all_t = [p["t"] for s in numeric for p in s["points"]]
    t1 = now
    t0 = min(all_t) if all_t else now - timedelta(days=1)
    if t1 - t0 < timedelta(days=1):
        t0 = t1 - timedelta(days=1)
    t0 -= (t1 - t0) * 0.04
    tick_fmt = "%b %d %H:%M" if t1 - t0 < timedelta(days=3) else "%b %d"
    claims = [s["baseline"] for s in numeric] + [p["claim"] for s in numeric for p in s["points"]]
    y_lo, y_hi = max(min(claims, default=0) - 6, 0), max(claims, default=100) + 6
    y_lo, y_hi = int(y_lo // 5) * 5, int(-(-y_hi // 5)) * 5

    def sx(t: datetime) -> float:
        return ML + (W - ML - MR) * (t - t0).total_seconds() / max((t1 - t0).total_seconds(), 1)

    def sy(v: float) -> float:
        return MT + (H - MT - MB) * (y_hi - v) / max(y_hi - y_lo, 1)

    out = [f'<svg viewBox="0 0 {W} {H}" class="record-chart" role="img" '
           'aria-labelledby="record-chart-title record-chart-desc">',
           '<title id="record-chart-title">Verification bounds across three frameworks</title>',
           '<desc id="record-chart-desc">Lower bounds rise and upper bounds fall. DAG and partial-disclosure '
           'lower records are separate series. Generic algorithms have no certified lower record; their pending '
           'line is outside the compression axis. The single upper series is the 106-cost generic candidate, '
           'with admission still pending. Hover or focus a record for its framework and solver.</desc>']
    for v in _nice_ticks(y_lo, y_hi):
        y = sy(v)
        out.append(f'<line class="grid" x1="{ML}" x2="{W - MR}" y1="{y:.1f}" y2="{y:.1f}"/>')
        out.append(f'<text class="tick" x="{ML - 8}" y="{y + 4:.1f}" text-anchor="end">{v}</text>')
    out.append(f'<line class="axis" x1="{ML}" x2="{W - MR}" y1="{H - MB}" y2="{H - MB}"/>')
    for t in _time_ticks(t0, t1):
        out.append(f'<text class="tick" x="{sx(t):.1f}" y="{H - MB + 20}" text-anchor="middle">{t.strftime(tick_fmt)}</text>')
    out.append(f'<text class="tick" x="4" y="{MT - 14}">compressions</text>')

    # Keep endpoint labels distinct even when different series have equal costs.
    ends = sorted(((sy(s["points"][-1]["claim"] if s["points"] else s["baseline"]), s["slug"])
                   for s in numeric))
    label_y = {}
    prev = MT - 28
    for y, slug in ends:
        label_y[slug] = max(y, prev + 28)
        prev = label_y[slug]
    overflow = max(prev - (H - MB - 4), 0)
    label_y = {slug: y - overflow for slug, y in label_y.items()}

    points = []
    for s in numeric:
        slug, label = escape(s["slug"]), escape(s["label"])
        cls = f'f-{s["framework"]} {s["kind"]}'
        pts, baseline = s["points"], s["baseline"]
        status = s.get("status", "certified")
        out.append(f'<g class="chart-series {cls}" data-series="{slug}" data-kind="{s["kind"]}" data-status="{status}">')
        # Retain the contract baseline before the first improvement.
        first_x = sx(pts[0]["t"]) if pts else sx(t1)
        baseline_label = "adapter; admission pending" if status == "candidate" else "contract baseline"
        out.append(f'<path class="line baseline" d="M{ML},{sy(baseline):.1f} H{first_x:.1f}"><title>{label}: {baseline} · {baseline_label}</title></path>')
        last_claim = pts[-1]["claim"] if pts else baseline
        if pts:
            d = f'M{first_x:.1f},{sy(baseline):.1f} V{sy(pts[0]["claim"]):.1f}'
            for p in pts[1:]:
                d += f' H{sx(p["t"]):.1f} V{sy(p["claim"]):.1f}'
            d += f' H{sx(t1):.1f}'
            out.append(f'<path class="line" d="{d}"/>')
        for p in pts:
            x, y = sx(p["t"]), sy(p["claim"])
            point = {"x": round(x, 1), "y": round(y, 1), "track": s["label"], "framework": s["framework"],
                     "kind": s["kind"], "claim": p["claim"], "login": p["login"],
                     "date": p["t"].strftime("%Y-%m-%d %H:%M UTC"), "id": p["id"], "demo": p.get("demo", False)}
            title = escape(f'{s["label"]}: {p["claim"]} compressions · {p["login"]} · {point["date"]}'
                           + (' · demo' if point["demo"] else ''))
            out.append(f'<a href="/submissions/{escape(p["id"])}" class="chart-record" data-point="{len(points)}" aria-label="{title}">'
                       f'<circle class="mark" cx="{x:.1f}" cy="{y:.1f}" r="4.5"><title>{title}</title></circle></a>')
            points.append(point)
        end_y, text_y = sy(last_claim), label_y[s["slug"]]
        out.append(f'<path class="connector" d="M{sx(t1):.1f},{end_y:.1f} L{sx(t1) + 12:.1f},{text_y:.1f} H{sx(t1) + 18:.1f}"/>')
        out.append(f'<text class="label" x="{sx(t1) + 23:.1f}" y="{text_y + 4:.1f}">{label} {last_claim}</text>')
        out.append('</g>')

    # This lane has no y-axis value. Pending never becomes a fabricated zero or a record point.
    for i, s in enumerate(pending):
        y = H - 30 + i * 24
        out.append(f'<g class="chart-series f-{s["framework"]} {s["kind"]} pending" data-series="{escape(s["slug"])}" '
                   f'data-kind="{s["kind"]}" data-status="pending">'
                   f'<path class="line" d="M{ML},{y} H{W - MR}"/>'
                   f'<text class="label" x="{W - MR + 23}" y="{y + 4}">{escape(s["label"])}: pending</text>'
                   f'<text class="tick" x="{ML}" y="{y - 10}">No certified bound · outside the numeric axis</text></g>')
    out.append(f'<line class="crosshair" x1="0" x2="0" y1="{MT}" y2="{H - MB}" visibility="hidden"/>')
    out.append('</svg>')
    return {"svg": '\n'.join(out), "points": json.dumps(points).replace('<', '\\u003c'), "series": series}
