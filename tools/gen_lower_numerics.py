#!/usr/bin/env python3
"""Generate the numeric certificate of the lower-bound proof for an operating point.

    tools/gen_lower_numerics.py [--a 21] [--K 500] [--Kp 450] [--qexp 110] [--Tmul 5] [--Texp 120] [--d0 113]
                                [--idx 2] [--v 22] [--slack 105] [--lean]

Prints: rTab (upper bounds on z_ℓ^(1/a) scaled by 2^20), cc (rational lower bound on exp(-T/N)),
the slack exponent, the rational success sum, the cost ratio, and a suggested threshold X with
cost/2^127 < X < success. Every rational is exact; the checks mirror the Lean statements.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import exp, factorial

ap = argparse.ArgumentParser()
ap.add_argument("--a", type=int, default=21); ap.add_argument("--K", type=int, default=500, help="ranks in the counting bound (M·β(d0) > K)")
ap.add_argument("--Kp", type=int, default=450, help="ranks the nonce search accepts and the success sum covers (b_l must stay >= 0)")
ap.add_argument("--qexp", type=int, default=110); ap.add_argument("--Tmul", type=int, default=5)
ap.add_argument("--Texp", type=int, default=120); ap.add_argument("--d0", type=int, default=113)
ap.add_argument("--idx", type=int, default=2); ap.add_argument("--v", type=int, default=22)
ap.add_argument("--slack", type=int, default=105, help="omega slack exponent: omega >= (T/N)(cc^l - 2^-slack)")
ap.add_argument("--lean", action="store_true", help="print the Lean rTab list")
o = ap.parse_args()
a, K, Kp, q, T, N = o.a, o.K, o.Kp, 2 ** o.qexp, o.Tmul * 2 ** o.Texp, 2 ** 128
den = 511 * K                       # z_l = 512 (l-1) / (511 K)
assert 512 * (Kp - 1) < den, f"z_Kp >= 1 (Kp = {Kp}, K = {K})"

# rTab[l-2] / 2^20 >= z_l^(1/a): smallest integer r with 512 (l-1) (2^20)^a <= 511 K r^a
def root_ub(l):
    lhs = 512 * (l - 1) * (2 ** 20) ** a
    lo, hi = 0, 2 ** 20 + 1
    while lo < hi:
        mid = (lo + hi) // 2
        if den * mid ** a >= lhs: hi = mid
        else: lo = mid + 1
    return lo
rTab = [root_ub(l) for l in range(2, Kp + 1)]
assert all(512 * (l - 1) * (2 ** 20) ** a <= den * rTab[l - 2] ** a for l in range(2, Kp + 1))
assert all(rTab[l - 2] <= 2 ** 20 for l in range(2, Kp + 1)), "z_l must stay < 1"

# cc: rational lower bound on exp(-T/N) via the alternating Taylor series (even truncation is >= exp for x<0? use n=4 with error bound)
x = F(T, N)
# exp(-x) >= 1 - x + x^2/2 - x^3/6  (alternating series, truncation after a negative term underestimates)
cc = 1 - x + x ** 2 / 2 - x ** 3 / 6
# the Lean proof compares cc with exp via Real.exp_bound (n = 4), whose remainder is |x|^4·5/96 < 2^-26 here,
# so round down by 2^-26 before truncating to 33 bits
cc_num = int((cc - F(1, 2 ** 26)) * 2 ** 33); cc = F(cc_num, 2 ** 33)
assert float(x) ** 4 * 5 / 96 < 2 ** -26
assert float(cc) <= exp(-float(x)), (float(cc), exp(-float(x)))

def bb(l):
    if l == 1: return F(1)
    r = F(rTab[l - 2], 2 ** 20); z = F(512 * (l - 1), den)
    return F(511, 512) * (1 - F(a, a - 1) * r + z / (a - 1))
slack = F(1, 2 ** o.slack)
gg = [x * (cc ** l - slack) * bb(l) for l in range(1, Kp + 1)]
bad = [l for l in range(1, Kp + 1) if bb(l) < 0]
assert not bad, f"bb negative at ranks {bad[:5]}... (lower Kp)"
assert all(cc ** l >= slack for l in range(1, Kp + 1))
S = F(256, 257) * sum(gg)
cost = 1024 + 2 ** 21 * o.idx + T * o.idx + (q + 2) * o.v + 2 * o.idx
ratio = F(cost, 2 ** 127)
print(f"a={a} K={K} (counting) Kp={Kp} (search/sum) q=2^{o.qexp} T={o.Tmul}·2^{o.Texp} d0={o.d0} idx={o.idx} v={o.v}")
print(f"smallest bb over 2..Kp: {min(float(bb(l)) for l in range(2, Kp + 1)):.2e} at rank {min(range(2, Kp + 1), key=lambda l: bb(l))}")
print(f"T/N = {x} ; cc = {cc_num}/2^33 (exp(-T/N) = {exp(-float(x)):.12f}, cc = {float(cc):.12f})")
print(f"success rational lower bound (with 256/257): {float(S):.6f}")
print(f"attack cost / 2^127 = {float(ratio):.6f}   (cost = {cost})")
for X in (F(2, 25), F(1, 12), F(3, 32), F(1, 10)):
    print(f"  threshold X = {X}: cost < X: {ratio < X}, X < success: {X < S}")
# slack adequacy for omega_ge: need x * l * (l/N) <= 2^-slack roughly; report
worst = float(x) * Kp * Kp / N
print(f"omega slack: x·K²/N = {worst:.3e} vs 2^-{o.slack} = {2.0 ** -o.slack:.3e}  -> {'ok' if worst < 2.0 ** -o.slack else 'TOO SMALL'}")
# counting factor and construction threshold checks
import math
rho = 5257 / o.d0
beta = math.prod(((a - 1) * rho / (1 + rho) + k) / (a * rho + k) for k in range(1, a + 1))
print(f"2^115·β_{a}(d0={o.d0}) = {2 ** 115 * beta:.1f} > K={K}: {2 ** 115 * beta > K}")
thr = math.log2(math.e * q * math.log(q))
print(f"log2(e q ln q) = {thr:.2f} > d0 = {o.d0}: {thr > o.d0}")
if o.lean:
    print("rTab :=", "[" + ", ".join(map(str, rTab)) + "]")
