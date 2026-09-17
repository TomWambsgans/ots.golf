"""The paper's concrete scheme, drawn faithfully as a radial necklace.

Root at the center; 7 subtree digests e_l around it; 3 group digests g_j under each; 3 hash chains
of 14 beads under each group, radiating outward to their 63 secret sources. One real signature is
lit on it: a cut of cost exactly 105 (revealed values, recomputed nodes, untouched beads), as in
Figure 1 of the paper.
"""
from __future__ import annotations

import math
from functools import lru_cache

CHAINS, LEN, PER_G, PER_E, NUM_E = 63, 14, 3, 3, 7
SIZE = 1100
CX = CY = SIZE / 2
R_E, R_G, R_TIP, STEP = 78, 140, 200, 15.5   # radii; beads t=14..0 from R_TIP outward


def angle(chain: int) -> float:
    return -math.pi / 2 + 2 * math.pi * chain / CHAINS


def polar(r: float, a: float) -> tuple[float, float]:
    return CX + r * math.cos(a), CY + r * math.sin(a)


def signature_cut() -> dict:
    """A cut of cost 105: three subtrees opened; in each the middle group opened and its three
    chains revealed low; every other digest revealed. Returns the status of every node."""
    open_e = {0, 2, 4}
    t_by_chain = {}
    ts = iter([3, 4, 2, 3, 3, 4, 4, 2, 4])          # Σ(14 − t) = 97 → cost 2 + 3·2 + 97 = 105
    revealed_g, revealed_e, open_g = set(), set(), set()
    for l in range(NUM_E):
        if l not in open_e:
            revealed_e.add(l)
            continue
        for j in range(3 * l, 3 * l + 3):
            if j == 3 * l + 1:
                open_g.add(j)
                for k in range(3 * j, 3 * j + 3):
                    t_by_chain[k] = next(ts)
            else:
                revealed_g.add(j)
    cost = 2 + sum(1 + 1 + sum(LEN - t_by_chain[k] for k in range(9 * l + 3, 9 * l + 6)) for l in open_e)
    assert cost == 105, cost
    return {"open_e": open_e, "open_g": open_g, "revealed_e": revealed_e, "revealed_g": revealed_g,
            "t": t_by_chain}


@lru_cache(maxsize=1)
def svg() -> str:
    cut = signature_cut()
    reach = R_TIP + LEN * STEP + 14                    # outermost source plus its diamond
    out = [f'<svg viewBox="{CX - reach:.0f} {CY - reach:.0f} {2 * reach:.0f} {2 * reach:.0f}" class="scheme-art" aria-hidden="true" focusable="false">']
    edges, nodes = [], []

    def status_chain(k: int, t: int) -> str:
        if k in cut["t"]:
            tk = cut["t"][k]
            return "revealed" if t == tk else ("recomputed" if t > tk else "untouched")
        return "untouched"

    for k in range(CHAINS):
        a = angle(k)
        j, l = k // PER_G, k // (PER_G * PER_E)
        g_open = j in cut["open_g"]
        # beads t = 14 (tip, nearest the group) .. 0 (source, outermost)
        pts = {t: polar(R_TIP + (LEN - t) * STEP, a) for t in range(LEN + 1)}
        for t in range(1, LEN + 1):
            (x1, y1), (x2, y2) = pts[t - 1], pts[t]
            st = status_chain(k, t) if g_open else "untouched"
            edges.append(f'<line class="e {st}" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
        for t in range(LEN + 1):
            x, y = pts[t]
            st = status_chain(k, t) if g_open else "untouched"
            if t == 0:
                s = 4.2
                nodes.append(f'<rect class="n src {st}" x="{x - s:.1f}" y="{y - s:.1f}" width="{2 * s:.1f}" '
                             f'height="{2 * s:.1f}" transform="rotate(45 {x:.1f} {y:.1f})"/>')
            else:
                nodes.append(f'<circle class="n bead {st}" cx="{x:.1f}" cy="{y:.1f}" r="3.4"/>')
        # tip -> group
        gx, gy = polar(R_G, angle(3 * j + 1))
        tx, ty = pts[LEN]
        st = "recomputed" if g_open else "untouched"
        edges.append(f'<line class="e {st}" x1="{tx:.1f}" y1="{ty:.1f}" x2="{gx:.1f}" y2="{gy:.1f}"/>')
    for j in range(CHAINS // PER_G):
        l = j // PER_E
        gx, gy = polar(R_G, angle(3 * j + 1))
        ex, ey = polar(R_E, angle(9 * l + 4))
        st = "revealed" if j in cut["revealed_g"] else ("recomputed" if j in cut["open_g"] else "untouched")
        est = "untouched" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e {est}" x1="{gx:.1f}" y1="{gy:.1f}" x2="{ex:.1f}" y2="{ey:.1f}"/>')
        nodes.append(f'<circle class="n g {st}" cx="{gx:.1f}" cy="{gy:.1f}" r="5.2"/>')
    for l in range(NUM_E):
        ex, ey = polar(R_E, angle(9 * l + 4))
        st = "revealed" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e recomputed" x1="{ex:.1f}" y1="{ey:.1f}" x2="{CX:.1f}" y2="{CY:.1f}"/>')
        nodes.append(f'<circle class="n e {st}" cx="{ex:.1f}" cy="{ey:.1f}" r="6.8"/>')
    nodes.append(f'<circle class="n root recomputed" cx="{CX:.1f}" cy="{CY:.1f}" r="11"/>')
    nodes.append(f'<circle class="n clasp" cx="{CX:.1f}" cy="{CY:.1f}" r="18"/>')
    out.extend(edges)
    out.extend(nodes)
    out.append("</svg>")
    return "\n".join(out)
