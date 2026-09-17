"""Illustrations for the rules page.

Every figure is drawn in one vocabulary, the one the home page's necklace uses: a secret source is
a diamond, a hash node a circle, a deterministic node a square, the root a filled circle. A lit
signature paints the revealed values orange, what the verifier recomputes blue, and leaves the rest
grey. The graphs are real graphs of the model: the recomputed set of a cut is obtained by the
statement's own rule (walk back from the root, stop at the cut), and the costs printed on the
figures come from the contract's block cost, not from a hand-typed number.

The SVGs carry no background of their own; they sit directly on the page.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from html import escape

OVERHEAD, BLOCK, HASH_BITS = 192, 512, 256


def block_cost(k: int) -> int:
    """`blockCost paperParams k` of Statement.lean: started 512-bit blocks of k + 192 bits."""
    return max(1, (k + OVERHEAD + BLOCK - 1) // BLOCK)


# ---------------------------------------------------------------- primitives

def _fmt(v: float) -> str:
    return f"{v:.1f}".rstrip("0").rstrip(".")


def line(x1, y1, x2, y2, cls="e") -> str:
    return f'<line class="{cls}" x1="{_fmt(x1)}" y1="{_fmt(y1)}" x2="{_fmt(x2)}" y2="{_fmt(y2)}"/>'


def circle(x, y, r, cls) -> str:
    return f'<circle class="{cls}" cx="{_fmt(x)}" cy="{_fmt(y)}" r="{_fmt(r)}"/>'


def square(x, y, s, cls) -> str:
    return (f'<rect class="{cls}" x="{_fmt(x - s)}" y="{_fmt(y - s)}" width="{_fmt(2 * s)}" '
            f'height="{_fmt(2 * s)}" rx="1.5"/>')


def diamond(x, y, s, cls) -> str:
    return (f'<rect class="{cls}" x="{_fmt(x - s)}" y="{_fmt(y - s)}" width="{_fmt(2 * s)}" '
            f'height="{_fmt(2 * s)}" transform="rotate(45 {_fmt(x)} {_fmt(y)})"/>')


def text(x, y, s, cls="t", anchor="middle") -> str:
    a = f' text-anchor="{anchor}"' if anchor else ""
    return f'<text class="{cls}" x="{_fmt(x)}" y="{_fmt(y)}"{a}>{s}</text>'


def sub(s: str) -> str:
    return f'<tspan baseline-shift="sub" font-size="75%">{s}</tspan>'


def sup(s: str) -> str:
    return f'<tspan baseline-shift="super" font-size="75%">{s}</tspan>'


def arrow_defs(name: str) -> str:
    return (f'<defs><marker id="ah-{name}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" '
            f'markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z"/></marker></defs>')


def arrow(name: str, d: str, cls="arrow") -> str:
    return f'<path class="{cls}" d="{d}" marker-end="url(#ah-{name})"/>'


def pill(x, y, w, h, label: str) -> str:
    return (f'<rect class="pill" x="{_fmt(x)}" y="{_fmt(y)}" width="{_fmt(w)}" height="{_fmt(h)}" rx="{_fmt(h / 2)}"/>'
            + text(x + w / 2, y + h / 2 + 4.5, label, "t strong"))


def svg(name: str, w: int, h: int, body: str, label: str) -> str:
    return (f'<svg class="fig-{name}" viewBox="0 0 {w} {h}" role="img" aria-label="{escape(label)}">'
            f"{body}</svg>")


# --------------------------------------------------------------- graph model

@dataclass
class Node:
    kind: str                     # "src" | "det" | "hash"
    parents: tuple[str, ...]
    bits: int
    x: float
    y: float
    tag: str = ""                 # small inline label (operation, width)
    side: str = "r"               # side of the tag: "l", "r" or "b" (below)


class Dag:
    """A computation graph of the model, with drawing coordinates."""

    R_HASH, R_ROOT, S_SRC, S_DET = 6.0, 8.0, 5.5, 5.2

    def __init__(self, nodes: dict[str, Node], root: str):
        self.nodes, self.root = nodes, root
        for n in nodes.values():
            if n.kind == "hash":
                assert len(n.parents) == 1 and n.bits == HASH_BITS
            if n.kind == "src":
                assert not n.parents

    def evaluated(self, cut: set[str]) -> set[str]:
        """`Graph.evaluated`: walk back from the root, stop at the cut; the visited nodes not in it."""
        seen: set[str] = set()
        stack = [self.root]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            if v not in cut:
                stack.extend(self.nodes[v].parents)
        return seen - cut

    def is_cut(self, cut: set[str]) -> bool:
        """The root is not revealed and no secret source is reached: `root_not_mem`, `no_hidden_source`."""
        return self.root not in cut and all(self.nodes[v].kind != "src" for v in self.evaluated(cut))

    def node_cost(self, v: str) -> int:
        n = self.nodes[v]
        return block_cost(self.nodes[n.parents[0]].bits) if n.kind == "hash" else 0

    def hash_costs(self, cut: set[str]) -> list[int]:
        """Costs of the recomputed hash nodes, root first, then in reading order."""
        ev = self.evaluated(cut)
        order = [self.root] + [v for v in self.nodes if v != self.root]
        return [self.node_cost(v) for v in order if v in ev and self.nodes[v].kind == "hash"]

    def reveal_bits(self, cut: set[str]) -> int:
        return sum(self.nodes[v].bits for v in cut)

    def keygen_cost(self) -> int:
        return sum(self.node_cost(v) for v in self.nodes)

    @staticmethod
    def width(bits: int) -> float:
        """Edge width for a value of `bits` bits: the eye sees which wires are wide."""
        return round(0.9 + bits / 300, 2)

    def radius(self, name: str) -> float:
        n = self.nodes[name]
        return self.R_ROOT if name == self.root else self.R_HASH if n.kind == "hash" else self.S_DET

    def draw(self, cut: set[str] | None = None, costs: str = "", fig: str = "g") -> str:
        """costs: "" for none, "evaluated" for the recomputed hash nodes, "all" for every hash node.
        `fig` prefixes the arrowhead marker ids, which must be unique on the page."""
        ev = self.evaluated(cut) if cut is not None else set()
        defs = "<defs>" + "".join(
            f'<marker id="ah-{fig}-{k}" class="ah {k}" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="7" '
            f'markerHeight="7" markerUnits="userSpaceOnUse" orient="auto"><path d="M0 0 L10 5 L0 10 z"/></marker>'
            for k in ("e", "rec")) + "</defs>"

        def status(v: str) -> str:
            if cut is None:
                return ""
            return " revealed" if v in cut else " recomputed" if v in ev else " untouched"

        edges, shapes, labels = [], [], []
        for name, n in self.nodes.items():
            for p in n.parents:
                q = self.nodes[p]
                dx, dy = n.x - q.x, n.y - q.y
                d = (dx * dx + dy * dy) ** 0.5 or 1.0
                k = (d - self.radius(name) - 1.5) / d          # stop at the child's border
                rec = name in ev
                e = line(q.x, q.y, q.x + dx * k, q.y + dy * k, "e recomputed" if rec else "e")
                edges.append(e.replace("/>", f' style="stroke-width:{_fmt(self.width(q.bits))}" '
                                             f'marker-end="url(#ah-{fig}-{"rec" if rec else "e"})"/>'))
            st = status(name)
            if n.kind == "src":
                shapes.append(diamond(n.x, n.y, self.S_SRC, "n src" + st))
            elif n.kind == "det":
                shapes.append(square(n.x, n.y, self.S_DET, "n det" + st))
            elif name == self.root:
                shapes.append(circle(n.x, n.y, self.R_ROOT, "n hash root" + st))
            else:
                shapes.append(circle(n.x, n.y, self.R_HASH, "n hash" + st))
            if n.tag:
                if n.side == "l":
                    labels.append(text(n.x - 11, n.y + 3.5, n.tag, "t tag", "end"))
                elif n.side == "b":
                    labels.append(text(n.x, n.y + 18, n.tag, "t tag", "middle"))
                else:
                    labels.append(text(n.x + 11, n.y + 3.5, n.tag, "t tag", "start"))
            if n.kind == "hash" and (costs == "all" or (costs == "evaluated" and name in ev)):
                cls = "t cost" if name in ev else "t cost faint"
                labels.append(text(n.x + 12, n.y + 4, str(self.node_cost(name)), cls, "start"))
        return defs + "".join(edges + shapes + labels)


def generic_graph() -> Dag:
    """A small graph that is a real DAG, not a tree: values of many widths (64 to 768 bits), a
    source and a truncated value each feeding two nodes, deterministic nodes of one, two and three
    parents (a selection of bits, an arbitrary function, concatenations), hash nodes over inputs of
    128, 384, 512 and 768 bits, costing one or two compressions each."""
    H = HASH_BITS
    nodes = {
        "s1": Node("src", (), 128, 80, 340, "128 b", "b"),
        "s2": Node("src", (), 256, 230, 340, "256 b", "b"),
        "s3": Node("src", (), 128, 300, 340, "128 b", "b"),
        "s4": Node("src", (), 128, 440, 340, "128 b", "b"),
        "h1": Node("hash", ("s1",), H, 80, 285),
        "t":  Node("det", ("h1",), 128, 80, 230, "first 128 b", "l"),
        "h2": Node("hash", ("t",), H, 80, 175),
        "f":  Node("det", ("h2",), 64, 80, 125, "any f · 64 b", "l"),
        "h5": Node("hash", ("f",), H, 80, 75),
        "c2": Node("det", ("s2", "s3"), 384, 265, 285, "concat · 384 b"),
        "h3": Node("hash", ("c2",), H, 265, 230),
        "c3": Node("det", ("t", "h3", "s4"), 512, 300, 175, "concat · 512 b"),
        "h4": Node("hash", ("c3",), H, 300, 120),
        "h6": Node("hash", ("s4",), H, 440, 285),
        "h7": Node("hash", ("h6",), H, 440, 230),
        "r0": Node("det", ("h5", "h4", "h7"), 768, 300, 65, "concat · 768 b"),
        "root": Node("hash", ("r0",), H, 300, 22),
    }
    return Dag(nodes, "root")


GENERIC_CUT = {"t", "h3", "s4"}


# ------------------------------------------------------------------ figures

def _legend_glyph(kind: str, x: float, y: float, cls: str = "") -> str:
    if kind == "src":
        return diamond(x, y, 5, "n src" + cls)
    if kind == "det":
        return square(x, y, 5, "n det" + cls)
    if kind == "root":
        return circle(x, y, 6.5, "n hash root" + cls)
    return circle(x, y, 5.5, "n hash" + cls)


def ots_flow() -> str:
    """Key generation, signing, verification; the one message."""
    N = "flow"
    b = [arrow_defs(N)]
    b.append(pill(30, 55, 120, 30, "KeyGen"))
    b.append(pill(290, 55, 120, 30, "Sign"))
    b.append(pill(540, 55, 120, 30, "Verify"))
    b.append(arrow(N, "M150 70 H288"))
    b.append(text(219, 62, "secret key sk"))
    b.append(arrow(N, "M410 70 H538"))
    b.append(text(474, 62, "signature σ"))
    b.append(arrow(N, "M90 85 V120 H600 V87"))
    b.append(text(345, 133, "public key pk"))
    b.append(arrow(N, "M350 32 V53"))
    b.append(text(350, 24, "the one message m"))
    b.append(arrow(N, "M600 32 V53"))
    b.append(text(600, 24, "m"))
    b.append(arrow(N, "M660 70 H695"))
    b.append(text(700, 74, "accept?", "t strong", "start"))
    return svg(N, 760, 150, "".join(b),
               "Key generation outputs a secret key and a public key; signing uses the secret key on one "
               "message; verification uses the public key, the message and the signature.")


def classics() -> str:
    """Lamport and Winternitz, drawn as graphs of the model with one signature lit on each."""
    H = HASH_BITS
    # Lamport on three message bits: a pair of secrets per bit, all hashes concatenated into the root.
    lam: dict[str, Node] = {}
    for b in range(3):
        for v in range(2):
            x = 70 + 100 * b + (-20 if v == 0 else 20)
            lam[f"s{b}{v}"] = Node("src", (), 128, x, 205)
            lam[f"h{b}{v}"] = Node("hash", (f"s{b}{v}",), H, x, 150)
    lam["cat"] = Node("det", tuple(f"h{b}{v}" for b in range(3) for v in range(2)), 6 * H, 170, 92)
    lam["root"] = Node("hash", ("cat",), H, 170, 48)
    L = Dag(lam, "root")
    bits = (0, 1, 1)
    lam_cut = {f"s{b}{v}" for b, v in enumerate(bits)} | {f"h{b}{1 - v}" for b, v in enumerate(bits)}
    assert L.is_cut(lam_cut)

    # Winternitz on three base-4 digits: a chain of three hashes per digit.
    win: dict[str, Node] = {}
    X0, YS = 480, (225, 195, 165, 135)
    for k in range(3):
        x = X0 + 60 * k
        win[f"w{k}0"] = Node("src", (), 128, x, YS[0])
        for t in range(1, 4):
            win[f"w{k}{t}"] = Node("hash", (f"w{k}{t - 1}",), H, x, YS[t])
    win["cat"] = Node("det", tuple(f"w{k}3" for k in range(3)), 3 * H, 540, 92)
    win["root"] = Node("hash", ("cat",), H, 540, 48)
    W = Dag(win, "root")
    digits = (1, 3, 0)
    win_cut = {f"w{k}{d}" for k, d in enumerate(digits)}
    assert W.is_cut(win_cut)

    b = [text(170, 18, "Lamport", "t strong"), text(540, 18, "Winternitz", "t strong")]
    b.append(L.draw(lam_cut, fig="lam"))
    for i, v in enumerate(bits):
        b.append(text(70 + 100 * i, 231, f"bit {i + 1} = {v}", "t muted"))
    b.append(text(170, 262, "a pair of secrets per message bit", "t muted"))
    b.append(text(170, 278, "sign bit b: reveal secret b, and the other hash", "t muted"))
    b.append(W.draw(win_cut, fig="win"))
    for t in range(4):
        b.append(text(X0 - 22, YS[t] + 3.5, str(t), "t muted", "end"))
    for k, d in enumerate(digits):
        b.append(text(X0 + 60 * k, 249, f"digit {d}", "t muted"))
    b.append(text(540, 262, "a hash chain per message digit (plus a checksum)", "t muted"))
    b.append(text(540, 278, "sign digit d: reveal position d, the verifier hashes upward", "t muted"))
    return svg("classics", 720, 288, "".join(b),
               "Lamport and Winternitz one-time signatures drawn as graphs: secret sources at the bottom, "
               "hash nodes above them, a concatenation and the root at the top, with one signature lit.")


def dag() -> str:
    """The generic graph, every hash node priced, with the legend of node kinds."""
    G = generic_graph()
    b = [G.draw(costs="all", fig="dag")]
    X, Y = 520, 40
    entries = [
        ("src", "secret source", ["uniformly random bits, any length"]),
        ("det", "deterministic node", ["any public function of any parents,", "any output length; costs nothing"]),
        ("hash", "hash node", ["H(label, input), 256-bit output;", "any input length, at (|input| + 192) / 512", "compressions rounded up (the blue numbers)"]),
        ("root", "root", ["the one hash node without children;", "public key = its first 128 bits"]),
    ]
    y = Y
    for kind, title, details in entries:
        b.append(_legend_glyph(kind, X + 7, y - 4))
        b.append(text(X + 22, y, title, "t strong", "start"))
        for j, d in enumerate(details):
            b.append(text(X + 22, y + 16 + 14 * j, d, "t muted", "start"))
        y += 30 + 14 * len(details)
    b.append(text(X + 7, y + 4, "wire width follows the bits carried;", "t muted", "start"))
    b.append(text(X + 7, y + 18, "a value may feed any number of nodes", "t muted", "start"))
    b.append(text(X + 7, y + 40, f"key generation: {G.keygen_cost()} compressions", "t muted", "start"))
    return svg("dag", 780, 370, "".join(b),
               "A computation graph of the model: four secret sources of 128 or 256 bits, deterministic nodes "
               "selecting bits, applying an arbitrary function and concatenating two or three values, hash nodes "
               "over 128 to 768 bits costing one or two compressions, values feeding several nodes, and the root.")


def dag_cut() -> str:
    """The generic graph with one disclosure set lit, and the cost of that signature worked out."""
    G = generic_graph()
    cut = GENERIC_CUT
    assert G.is_cut(cut)
    costs = G.hash_costs(cut)
    total = sum(costs)
    b = [G.draw(cut, costs="evaluated", fig="cut")]
    X, Y = 520, 60
    b.append(circle(X + 7, Y - 4, 5.5, "n hash revealed"))
    b.append(text(X + 22, Y, "revealed", "t strong", "start"))
    b.append(text(X + 22, Y + 16, f"the signature: {G.reveal_bits(cut)} bits of values", "t muted", "start"))
    b.append(circle(X + 7, Y + 48, 5.5, "n hash recomputed"))
    b.append(text(X + 22, Y + 52, "recomputed by the verifier", "t strong", "start"))
    b.append(text(X + 22, Y + 68, f"{len(costs)} hash nodes: {' + '.join(map(str, costs))} = {total}", "t muted", "start"))
    b.append(circle(X + 7, Y + 100, 5.5, "n hash untouched"))
    b.append(text(X + 22, Y + 104, "never touched", "t strong", "start"))
    b.append(text(X + 22, Y + 120, "below the cut, still secret", "t muted", "start"))
    b.append(text(X + 7, Y + 166, "verification cost", "t strong", "start"))
    b.append(text(X + 7, Y + 184, f"2 (index) + {total} = {2 + total} compressions", "t muted", "start"))
    return svg("cut", 780, 370, "".join(b),
               "The same graph with one disclosure set lit: three revealed values (one of them a secret source), "
               "the nodes the verifier recomputes above them with their costs, and the untouched nodes below.")


# --------------------------------------------------------------- bit flow

BIT, BAR = 0.42, 14          # px per bit, bar height


def _bar(x: float, y: float, bits: int, cls: str, label: str = "") -> str:
    w = bits * BIT
    out = f'<rect class="bb {cls}" x="{_fmt(x)}" y="{_fmt(y)}" width="{_fmt(w)}" height="{BAR}" rx="2"/>'
    if label:
        out += text(x + w / 2, y + BAR / 2 + 3.3, label, "t bl")
    return out


def _rib(x1a: float, x1b: float, y1: float, x2a: float, x2b: float, y2: float, cls: str) -> str:
    """A ribbon carrying the bits [x1a, x1b] at height y1 to [x2a, x2b] at height y2."""
    ym = (y1 + y2) / 2
    d = (f"M{_fmt(x1a)},{_fmt(y1)} C{_fmt(x1a)},{_fmt(ym)} {_fmt(x2a)},{_fmt(ym)} {_fmt(x2a)},{_fmt(y2)} "
         f"L{_fmt(x2b)},{_fmt(y2)} C{_fmt(x2b)},{_fmt(ym)} {_fmt(x1b)},{_fmt(ym)} {_fmt(x1b)},{_fmt(y1)} Z")
    return f'<path class="rib {cls}" d="{d}"/>'


def _hash(b: list[str], x0: float, x1: float, y_in: float, cx: float, cy: float, out_x: float, out_y: float,
          in_bits: int, cls: str, label: str) -> int:
    """Input bits [x0, x1] leaving height y_in funnel into H at (cx, cy) and come out as a fresh 256-bit
    value at (out_x, out_y). Returns the cost."""
    cost = block_cost(in_bits)
    b.append(_rib(x0, x1, y_in, cx - 6, cx + 6, cy - 8, cls))
    b.append(_rib(cx - 6, cx + 6, cy + 8, out_x, out_x + HASH_BITS * BIT, out_y, cls))
    b.append(circle(cx, cy, 8, "n hash"))
    b.append(text(cx, cy + 3.3, "H", "t hl"))
    b.append(text(cx + 12, cy + 4, str(cost), "t cost", "start"))
    b.append(_bar(out_x, out_y, HASH_BITS, cls, label))
    return cost


def bit_flow() -> str:
    """Values as bars, bits as ribbons: four secret sources of 64 to 256 bits are split, sliced,
    transformed by an arbitrary function, reused and concatenated for free, and hashed into fresh
    256-bit values at various costs, down to a root whose first 128 bits are the public key."""
    Y = [22, 84, 146, 208, 270, 332, 394, 446]           # tops of the bars, row by row
    bot = [y + BAR for y in Y]
    mid = [(bot[i] + Y[i + 1]) / 2 for i in range(len(Y) - 1)]  # heights of the hash circles
    W = lambda n: n * BIT
    b: list[str] = []
    costs = []
    # row 0: the secret sources
    A, B, C, D = 40, 200, 360, 480
    b += [_bar(A, Y[0], 128, "bits-a", "A · 128 b"), _bar(B, Y[0], 256, "bits-b", "B · 256 b"),
          _bar(C, Y[0], 64, "bits-c"), text(C + W(64) / 2, Y[0] - 5, "C · 64 b", "t tag"),
          _bar(D, Y[0], 128, "bits-d", "D · 128 b")]
    # row 1: H₁ = H(A); B split in two; E = f(C), an arbitrary function with a 96-bit output
    H1 = 40
    costs.append(_hash(b, A, A + W(128), bot[0], A + W(128) / 2, mid[0], H1, Y[1], 128, "bits-h1", "H₁ = H(A) · 256 b"))
    BL, BH = 190, 254
    b += [_rib(B, B + W(128), bot[0], BL, BL + W(128), Y[1], "bits-b"),
          _rib(B + W(128), B + W(256), bot[0], BH, BH + W(128), Y[1], "bits-b"),
          _bar(BL, Y[1], 128, "bits-b", "B[:128]"), _bar(BH, Y[1], 128, "bits-b", "B[128:]")]
    E, fx = 353, C + W(64) / 2
    b += [_rib(C, C + W(64), bot[0], fx - 6, fx + 6, mid[0] - 7, "bits-c"),
          _rib(fx - 6, fx + 6, mid[0] + 7, E, E + W(96), Y[1], "bits-f"),
          square(fx, mid[0], 7, "n det"), text(fx, mid[0] + 3.3, "f", "t hl"),
          text(fx + 12, mid[0] + 4, "any function", "t tag", "start"),
          _bar(E, Y[1], 96, "bits-f", "f(C) · 96 b")]
    # row 2: T = H₁[:128]; C1 = B[128:] ‖ D; C2 = B[:128] ‖ f(C) ‖ D  (D is used twice)
    T, C1, C2 = 40, 250, 400
    b += [_rib(H1, H1 + W(128), bot[1], T, T + W(128), Y[2], "bits-h1"), _bar(T, Y[2], 128, "bits-h1", "H₁[:128]")]
    b += [_rib(BH, BH + W(128), bot[1], C1, C1 + W(128), Y[2], "bits-b"),
          _rib(D, D + W(128), bot[0], C1 + W(128), C1 + W(256), Y[2], "bits-d"),
          _bar(C1, Y[2], 128, "bits-b", "B[128:]"), _bar(C1 + W(128), Y[2], 128, "bits-d", "D")]
    b += [_rib(BL, BL + W(128), bot[1], C2, C2 + W(128), Y[2], "bits-b"),
          _rib(E, E + W(96), bot[1], C2 + W(128), C2 + W(224), Y[2], "bits-f"),
          _rib(D, D + W(128), bot[0], C2 + W(224), C2 + W(352), Y[2], "bits-d"),
          _bar(C2, Y[2], 128, "bits-b", "B[:128]"), _bar(C2 + W(128), Y[2], 96, "bits-f", "f(C)"),
          _bar(C2 + W(224), Y[2], 128, "bits-d", "D")]
    # row 3: C3 = T ‖ C1 (384 bits); H₂ = H(C2), 352 bits in
    C3, H2 = 160, 420
    b += [_rib(T, T + W(128), bot[2], C3, C3 + W(128), Y[3], "bits-h1"),
          _rib(C1, C1 + W(128), bot[2], C3 + W(128), C3 + W(256), Y[3], "bits-b"),
          _rib(C1 + W(128), C1 + W(256), bot[2], C3 + W(256), C3 + W(384), Y[3], "bits-d"),
          _bar(C3, Y[3], 128, "bits-h1", "H₁[:128]"), _bar(C3 + W(128), Y[3], 128, "bits-b", "B[128:]"),
          _bar(C3 + W(256), Y[3], 128, "bits-d", "D")]
    costs.append(_hash(b, C2, C2 + W(352), bot[2], C2 + W(352) / 2, mid[2], H2, Y[3], 352, "bits-h2", "H₂ · 256 b"))
    # row 4: H₃ = H(C3), 384 bits in
    H3 = 186
    costs.append(_hash(b, C3, C3 + W(384), bot[3], C3 + W(384) / 2, mid[3], H3, Y[4], 384, "bits-h3", "H₃ · 256 b"))
    # row 5: R = H₁[192:] ‖ H₃ ‖ H₂ (576 bits): a slice of H₁ travels four rows down
    R = 100
    b += [_rib(H1 + W(192), H1 + W(256), bot[1], R, R + W(64), Y[5], "bits-h1"),
          _rib(H3, H3 + W(256), bot[4], R + W(64), R + W(320), Y[5], "bits-h3"),
          _rib(H2, H2 + W(256), bot[3], R + W(320), R + W(576), Y[5], "bits-h2"),
          _bar(R, Y[5], 64, "bits-h1"), _bar(R + W(64), Y[5], 256, "bits-h3", "H₃"),
          _bar(R + W(320), Y[5], 256, "bits-h2", "H₂"), text(R + W(32), Y[5] + BAR + 11, "H₁[192:]", "t tag")]
    # row 6: the root = H(R), 576 bits in; row 7: pk = root[:128]
    RT = R + W(576) / 2 - W(256) / 2
    costs.append(_hash(b, R, R + W(576), bot[5], R + W(576) / 2, mid[5], RT, Y[6], 576, "bits-root", "root · 256 b"))
    b += [_rib(RT, RT + W(128), bot[6], RT, RT + W(128), Y[7], "bits-root"),
          _bar(RT, Y[7], 128, "bits-pk", "pk · 128 b"),
          text(RT + W(128) + 8, Y[7] + BAR / 2 + 3.5, "the other 128 bits of the root are never used", "t tag", "start")]
    # legend
    X, y = 586, 30
    rows = [
        ("A B C D", "secret sources", ["uniformly random bits, 64 to 256 here"]),
        ("H", "hash node", ["any input in, 256 fresh bits out, at", "(|input| + 192) / 512 compressions", "rounded up (the blue numbers)"]),
        ("f", "deterministic node", ["any public function, any output length"]),
        ("~", "ribbons", ["bits on the move: split, sliced, reused,", "concatenated, and all of it free"]),
    ]
    for glyph, title, lines in rows:
        if glyph == "H":
            b += [circle(X + 7, y - 4, 7, "n hash"), text(X + 7, y - 0.7, "H", "t hl")]
        elif glyph == "f":
            b += [square(X + 7, y - 4, 6.5, "n det"), text(X + 7, y - 0.7, "f", "t hl")]
        elif glyph == "~":
            b.append(_rib(X, X + 14, y - 11, X, X + 14, y + 3, "bits-b"))
        else:
            for i, c in enumerate("abcd"):
                b.append(f'<rect class="bb bits-{c}" x="{_fmt(X + 3.5 * i)}" y="{_fmt(y - 10)}" width="3" height="12" rx="1"/>')
        b.append(text(X + 22, y, title, "t strong", "start"))
        for j, ln in enumerate(lines):
            b.append(text(X + 22, y + 16 + 14 * j, ln, "t muted", "start"))
        y += 32 + 14 * len(lines)
    b.append(text(X + 7, y + 6, f"key generation: {' + '.join(map(str, costs))} = {sum(costs)}", "t muted", "start"))
    b.append(text(X + 7, y + 20, "compressions", "t muted", "start"))
    return svg("bits", 810, 480, "".join(b),
               "Bits flowing through a scheme: four secret sources of 64 to 256 bits are split, sliced, passed "
               "through an arbitrary function, reused and concatenated for free, and hashed into fresh 256-bit "
               "values costing one or two compressions each, down to a root whose first 128 bits are the public key.")


def cost_ruler() -> str:
    """Inputs of several lengths against 512-bit blocks, each preceded by the 192 overhead bits."""
    X0, BW = 240, 130              # left edge of block 1, pixels per 512-bit block
    px = BW / BLOCK
    rows = [
        ("chain step: a 128-bit value", 128),
        ("a 256-bit digest", 256),
        ("index query H(enc, m ‖ η), 512 bits", 512),
        ("root of the record: 41 × 128 bits", 41 * 128),
    ]
    b = ['<defs><pattern id="hatch" class="hatch" width="6" height="6" patternUnits="userSpaceOnUse" '
         'patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="6"/></pattern></defs>']
    for k in range(4):
        x = X0 + BW * k
        b.append(line(x, 30, x, 166, "blockline"))
        if k < 3:
            b.append(text(x + BW / 2, 22, f"block {k + 1}", "t muted"))
    for i, (label, bits) in enumerate(rows):
        y = 48 + 32 * i
        b.append(text(X0 - 14, y + 4, label, "t", "end"))
        over = OVERHEAD * px
        b.append(f'<rect class="over" fill="url(#hatch)" x="{_fmt(X0)}" y="{_fmt(y - 7)}" width="{_fmt(over)}" height="14"/>')
        full = bits * px
        xend = X0 + over + full
        if xend <= X0 + 3 * BW - 8:
            b.append(f'<rect class="bar" x="{_fmt(X0 + over)}" y="{_fmt(y - 7)}" width="{_fmt(full)}" height="14"/>')
        else:                       # too long to draw: a break
            xb = X0 + 3 * BW - 36
            b.append(f'<rect class="bar" x="{_fmt(X0 + over)}" y="{_fmt(y - 7)}" width="{_fmt(xb - X0 - over)}" height="14"/>')
            b.append(f'<rect class="bar" x="{_fmt(xb + 14)}" y="{_fmt(y - 7)}" width="18" height="14"/>')
            b.append(line(xb + 3, y + 10, xb + 7, y - 10, "brk"))
            b.append(line(xb + 8, y + 10, xb + 12, y - 10, "brk"))
        c = block_cost(bits)
        b.append(text(X0 + 3 * BW + 16, y + 4, f"{c} compression{'s' if c > 1 else ''}", "t strong", "start"))
    y = 190
    b.append(f'<rect class="over" fill="url(#hatch)" x="{_fmt(X0)}" y="{_fmt(y - 8)}" width="16" height="11"/>')
    b.append(text(X0 + 22, y, "192 overhead bits: public parameter ‖ tweak", "t muted", "start"))
    b.append(f'<rect class="bar" x="{_fmt(X0 + 280)}" y="{_fmt(y - 8)}" width="16" height="11"/>')
    b.append(text(X0 + 302, y, "the input", "t muted", "start"))
    return svg("cost", 800, 200, "".join(b),
               "Four hash inputs laid against 512-bit blocks, each preceded by 192 overhead bits: a 128-bit "
               "chain step and a 256-bit digest cost one compression, the 512-bit index query two, the "
               "record's 5248-bit root eleven.")


def experiment() -> str:
    """The one-signature forgery game as a sequence diagram."""
    N = "exp"
    b = [arrow_defs(N)]
    b.append(pill(60, 14, 120, 28, "challenger"))
    b.append(text(120, 58, "runs KeyGen, Sign, Verify", "t muted"))
    b.append(pill(580, 14, 120, 28, "attacker"))
    b.append(text(640, 58, "any strategy; only its queries cost", "t muted"))
    b.append(circle(380, 28, 14, "n hash"))
    b.append(text(380, 32.5, "H", "t strong"))
    b.append(arrow(N, "M366 28 H184", "arrow dashed"))
    b.append(arrow(N, "M394 28 H576", "arrow dashed"))
    b.append(text(380, 58, "the random oracle, shared", "t muted"))
    b.append(line(120, 66, 120, 188, "life"))
    b.append(line(640, 66, 640, 188, "life"))
    steps = [
        (86, ">", "the public key pk"),
        (116, "<", f"a message m{sub('1')} of the attacker's choice"),
        (146, ">", f"σ{sub('1')} = Sign(sk, m{sub('1')}), the only signature"),
        (176, "<", f"a forgery (m{sub('2')}, σ{sub('2')}) ≠ (m{sub('1')}, σ{sub('1')})"),
    ]
    for y, d, label in steps:
        b.append(arrow(N, f"M124 {y} H636" if d == ">" else f"M636 {y} H124"))
        b.append(text(380, y - 8, label))
    b.append(text(380, 212, f"the attacker wins if Verify(pk, m{sub('2')}, σ{sub('2')}) accepts", "t strong"))
    return svg(N, 760, 222, "".join(b),
               "The forgery experiment: the challenger sends the public key, the attacker chooses one message "
               "and receives its signature, then outputs a different message-signature pair that must be "
               "accepted.")


def interval(lo: int, up: int) -> str:
    """A number line with the two records; the optimum lies between them."""
    top = 125 if up <= 118 else int(up * 1.12 // 25 + 1) * 25
    X0, W = 30, 660
    k = W / top
    xl, xu = X0 + lo * k, X0 + up * k
    b = [line(X0, 60, X0 + W + 10, 60, "axis")]
    step = 25 if top <= 200 else 50
    for v in range(0, top + 1, step):
        x = X0 + v * k
        b.append(line(x, 60, x, 66, "tick"))
        b.append(text(x, 80, str(v), "t ticklab"))
    b.append(f'<rect class="gap" x="{_fmt(xl)}" y="{48}" width="{_fmt(xu - xl)}" height="24"/>')
    b.append(text((xl + xu) / 2, 103, "the optimum is in here", "t muted"))
    b.append(line(xl, 40, xl, 72, "mark s1"))
    b.append(text(xl, 32, f"lower bound {lo}", "t mlab s1"))
    b.append(f'<path class="arr s1" d="M{_fmt(xl + 6)} 60 h18 l-6 -4 m6 4 l-6 4"/>')
    b.append(line(xu, 40, xu, 72, "mark s2"))
    b.append(text(xu, 32, f"upper bound {up}", "t mlab s2"))
    b.append(f'<path class="arr s2" d="M{_fmt(xu - 6)} 60 h-18 l6 -4 m-6 4 l6 4"/>')
    return svg("interval", 720, 110, "".join(b),
               f"A number line from 0 to {top} compressions with the lower-bound record at {lo} and the "
               f"upper-bound record at {up}; the optimum lies between them.")


@lru_cache(maxsize=None)
def static() -> dict[str, str]:
    """The figures that do not depend on the records."""
    return {
        "flow": ots_flow(),
        "classics": classics(),
        "dag": dag(),
        "bits": bit_flow(),
        "cut": dag_cut(),
        "cost": cost_ruler(),
        "experiment": experiment(),
    }


def all_figures(lo: int, up: int) -> dict[str, str]:
    return {**static(), "interval": interval(lo, up)}
