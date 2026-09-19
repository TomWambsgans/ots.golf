# Bare-oracle lower-bound numerical investigation

The entropy calculations below are conditional; the final section checks the exact arithmetic
of the officially verified pattern attack at 18. The proposed fresh-weight construction and information inequalities in
the handoff were refuted during the mathematical audit: hidden earlier duplicate
queries can put the charged weight outside the reconstructed/target set. These
numbers therefore do not justify the proposed attack. Valid replacement
inequalities would be required before they could support a certificate. The
Python search uses floating-point logarithms and exponentials; its success
probability replaces `(1-x)^T` by `exp(-x*T)`.

## Bell-number correction

The handoff's suggested budget `S*=5309` is too small for the stated Bell union
bound, with original disclosure budget 5248 and failure allowance `epsilon=2^-9`.
The sufficient integer budget is

```
S* = 5248 + 9 + ceil(log2 Bell(|E_i|)).
```

Exact integer recurrence gives:

| Maximum reconstructed hash nodes | Bell number | log2 (approximate) | Sufficient integer S* |
| --- | ---: | ---: | ---: |
| 22 | 4506715738447323 | 52.000997878 | 5310 |
| 23 | 44152005855084346 | 55.293328500 | 5313 |

For proposed claim 24, the contrary assumption `verifyCost <= 23` leaves
reconstruction cost at most 22, so `|E_i| <= 22` and `a=|V_i| <= 21`.
Consequently 5310 is the sufficient integer budget **if the proposed Bell
information inequality holds**. Budget 5313 also works numerically and covers
the more conservative 23-node cap. In particular `Bell(22) > 2^52`, so rounding
its logarithm down to 52 is not valid.

## Simple integer operating point for proposed claim 24

Keep the historical integer choices

```
a = 21, v = 22, K = 100, d0 = 123,
q = 5 * 2^113, T = 3 * 2^121, idx = 1.
```

The tool computes the counting product and cost with Python `Fraction`, so
comparisons of those quantities against rational thresholds are exact:

| S* | `2^115 beta_21(123)` (decimal display) | Exact comparison |
| ---: | ---: | --- |
| 5309 | 2530.842137377 | > 100 |
| 5310 | 2521.121673523 | > 100 |
| 5313 | 2492.194254118 | > 100 |

The construction threshold is approximately
`log2(e*q*ln(q)) = 123.085379816 > 123`; the existing Lean proof of this inequality
uses the same q and needs no numerical change. The cost is

```
B = 1024 + 2^20 + T + (q+2)*22 + 2,
B / 2^127 < 27/500,
B / 2^127 approximately 0.053588867.
```

The modeled success with exponent 21 is approximately 0.058102608, leaving
margin approximately 0.004513741 before any bare/separated-oracle coupling loss.
The handoff's proposed `2^-135` loss, if proved, is far below that margin.

There is a simpler way to retain the old exact success certificate. Once the
counting argument proves, for `0 < d <= 123`,

```
2^115 beta_21(d) >= 100 * (d/123)^21,
```

use `(d/123)^21 >= (d/123)^22` to obtain the historical exponent-22 rank bound.
The existing `NumericsSuccess.lean` certificate proves success greater than
`11/200` from that rank bound. Its rational table, K, q, T, and nonce weights do
not need regeneration. The old conservative reconstruction cost 23 also remains
an upper bound and gives cost less than `27/500`. Thus the old success certificate
has a rational margin greater than `1/1000`, conditional on the new mathematical
lemmas and on a proved coupling loss smaller than that margin. This observation
is a porting route, not an assertion that the bare-oracle theorem is proved.

## Search results and proposed claim 25

Commands run:

```
python3 tools/tune_lower_bound.py --method entropy --s-star 5309 --idx 1 --claims 24,25
python3 tools/tune_lower_bound.py --method entropy --s-star 5310 --idx 1 --claims 24 --no-search
python3 tools/tune_lower_bound.py --method entropy --s-star 5313 --idx 1 --claims 24,25
```

The coarse grid for proposed claim 24 found estimated margins 0.1111409 at
S*=5309 and 0.1110472 at S*=5313 (K=1600, T=2^123). These points have no associated
Lean success certificate; the simple K=100 point is easier to port.

For proposed claim 25 the historical a=22, K=100, d0=123 point has counting
product only 83.963921411 at S*=5309 and 82.621160151 at S*=5313. It fails the
required strict counting inequality. The original grid retuning found no
positive margin: its best estimated margins were -0.0006810 and -0.0007077,
respectively. A refined floating-point search over every K from 25 through 400, using the
smallest feasible real q and continuous optimization in `log2 T` from 118 to 125,
also found no positive margin: the best values were -0.0005523 at S*=5309 and
-0.0005628 at S*=5313. A negative search result is not an impossibility proof.

The labeled-model historical check remains consistent: S*=5257, a=22 has
counting product 103.652830396, estimated success 0.056586715, and cost ratio
0.053894043. This is historical validation of the numerical formulas only.

## Tool changes

In entropy mode, `tools/tune_lower_bound.py` accepts `--s-star`, explicitly labels output as
conditional exploration, validates parameter ranges, reports exact Bell numbers,
and checks simple integer-point counting and cost inequalities with fractions.
`--no-search` reports only those points. Exponential differences use `expm1` to
avoid subtracting nearby floats. The q grid is reduced to its first feasible
point for each K: once the construction threshold is met, the success formula
is independent of q and the cost strictly increases in q. This preserves the
original grid optimum while making the full search fast.


## Exact reconstruction-pattern calculation

The replacement attack uses no entropy budget. Running
`python3 tools/tune_lower_bound.py --idx 1 --claims 18,19` uses integer binomial coefficients
and exact rational arithmetic throughout. For 18 the pattern bound is

```
sum(k=0..15, choose(1023,k)) = 984793598840378644322567920484352 < 2^110.
```

The conservative inequalities used by Lean are: at least three quarters of indices have
at least eight equal patterns; signing selects such an index with probability at least
one half from a fresh message domain; each of the two uniform-message choices retains
at least nine tenths of the mass; and `2^122` nonce trials hit eight targets with probability
at least `1/9`. Hence success is at least `9/200`. With reconstruction cost at most 16,
`B=1024+2^20+2^122+34` has `B/2^127 < 1/25`. The tool checks these comparisons exactly.
Its tighter rational success estimate is about 0.089686955, but the certificate only needs
the conservative 0.045 bound.

For 19 the corresponding pattern count is
`62105400126157768832237678313804609 > 2^115`, so this counting argument supplies no
positive good-class fraction. That is a limitation of this method, not an upper bound.
The tool now defaults to the pattern calculation at 18. Select `--method entropy` to reproduce
the historical conditional numerical searches above; their false transfer lemmas remain false.
