# Generic verification lower bound: one compression

`Solution.lean` exports `OptimalOTS.Challenge.GenericLower.candidate` with claim 1.
It quantifies over arbitrary oracle algorithms satisfying perfect correctness, signing success
at least one half, the paper size and resource limits, and 127-bit weak unforgeability.

A zero-cost verifier makes no oracle queries. For every public key on which honest signing a
fixed message can succeed, correctness gives a signature accepted with probability one by this
oracle-independent verifier. A free classical selection chooses such a signature from public
data. The attacker signs message 0 and forges message 1; its success is at least one half and
its complete experiment costs at most 1024 + 2^21, contradicting security.

`Costs.lean` proves structural cost rules, `ZeroQuery.lean` proves oracle independence, and
`Proof.lean` constructs the attack. All proof code is in this submission root. Only the generic
definitions are protected; the lower theorem is not assumed by the contract.

Run `python3 verifier/verify.py generic-lower --source .` from the repository root.
