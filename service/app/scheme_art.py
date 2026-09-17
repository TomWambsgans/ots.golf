"""The concrete scheme, drawn faithfully as a radial necklace.

Root at the center; 41 hash chains of 20 beads radiating outward to their secret sources, their
ends hashed together into the root. One real signature is lit on it: one revealed value per chain,
at positions whose recomputation costs exactly 96 chain hashes (revealed values, recomputed nodes,
untouched beads), as in the paper's figure.
"""
from __future__ import annotations

import math
from functools import lru_cache

CHAINS, LEN, STEPS = 41, 20, 96
SIZE = 1100
CX = CY = SIZE / 2
R_TIP, STEP = 120, 15.5   # radius of the chain ends; beads t=20..0 from R_TIP outward


def angle(chain: int) -> float:
    return -math.pi / 2 + 2 * math.pi * chain / CHAINS


def polar(r: float, a: float) -> tuple[float, float]:
    return CX + r * math.cos(a), CY + r * math.sin(a)


def signature_positions() -> list[int]:
    """Revealed positions t_k (0 = source, 20 = chain end) with sum(20 - t_k) = 96: a gentle wave,
    so that the lit chains read as a pattern rather than noise."""
    base = [20 - int(round(2.34 + 2.0 * math.sin(2 * math.pi * k / CHAINS * 3))) for k in range(CHAINS)]
    steps = sum(LEN - t for t in base)
    k = 0
    while steps != STEPS:                       # nudge to the exact target
        if steps < STEPS and base[k] > 0:
            base[k] -= 1; steps += 1
        elif steps > STEPS and base[k] < LEN:
            base[k] += 1; steps -= 1
        k = (k + 1) % CHAINS
    assert sum(LEN - t for t in base) == STEPS
    return base


@lru_cache(maxsize=1)
def svg() -> str:
    pos = signature_positions()
    reach = R_TIP + LEN * STEP + 14
    out = [f'<svg viewBox="{CX - reach:.0f} {CY - reach:.0f} {2 * reach:.0f} {2 * reach:.0f}" '
           'class="scheme-art" aria-hidden="true" focusable="false">']
    edges, nodes = [], []
    for k in range(CHAINS):
        a = angle(k)
        tk = pos[k]
        pts = {t: polar(R_TIP + (LEN - t) * STEP, a) for t in range(LEN + 1)}   # t = 20 innermost

        def status(t: int) -> str:
            return "revealed" if t == tk else ("recomputed" if t > tk else "untouched")

        for t in range(1, LEN + 1):
            (x1, y1), (x2, y2) = pts[t - 1], pts[t]
            edges.append(f'<line class="e {status(t)}" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
        for t in range(LEN + 1):
            x, y = pts[t]
            if t == 0:
                s = 4.2
                nodes.append(f'<rect class="n src {status(t)}" x="{x - s:.1f}" y="{y - s:.1f}" width="{2 * s:.1f}" '
                             f'height="{2 * s:.1f}" transform="rotate(45 {x:.1f} {y:.1f})"/>')
            else:
                nodes.append(f'<circle class="n bead {status(t)}" cx="{x:.1f}" cy="{y:.1f}" r="3.4"/>')
        tx, ty = pts[LEN]
        edges.append(f'<line class="e recomputed" x1="{tx:.1f}" y1="{ty:.1f}" x2="{CX:.1f}" y2="{CY:.1f}"/>')
    nodes.append(f'<circle class="n root recomputed" cx="{CX:.1f}" cy="{CY:.1f}" r="11"/>')
    nodes.append(f'<circle class="n clasp" cx="{CX:.1f}" cy="{CY:.1f}" r="18"/>')
    out.extend(edges)
    out.extend(nodes)
    out.append("</svg>")
    return "\n".join(out)
