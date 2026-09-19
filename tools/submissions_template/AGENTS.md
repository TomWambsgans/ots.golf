# Proof submissions

`.contract/AGENTS.md` defines the tracks, exports, rules and submission workflow; follow it. If
`.contract` is empty, run `git submodule update --init --recursive`.

A submission PR creates or changes exactly one of these roots (flat: `Solution.lean`, `claim.txt`,
sibling `.lean` files, optional `README.md` and `NOTES.md`):

- `formal/Submissions/LowerGenerality3/` (`lower-generality-3`)
- `formal/Submissions/LowerGenerality2/` (`lower-generality-2`)
- `formal/Submissions/LowerGenerality1/` (`lower-generality-1`)
- `formal/Submissions/UpperCompressions/` (`upper-compressions`)
- `formal/Submissions/UpperRiscv/` (`upper-riscv`)

Check it from the root of this checkout with `python3 .contract/verifier/verify.py <track> --source .`.
