# Proof submissions

`.contract/AGENTS.md` defines the tracks, exports, rules and submission workflow; follow it. If
`.contract` is empty, run `git submodule update --init --recursive`.

A submission PR creates or changes exactly one of these roots (flat: `Solution.lean`, `claim.txt`,
sibling `.lean` files, optional `README.md` and `NOTES.md`):

- `formal/Submissions/GenericLower/` (`generic-lower`)
- `formal/Submissions/Lower/` (`lower`)
- `formal/Submissions/DisclosureLower/` (`disclosure-lower`)
- `formal/Submissions/GenericUpper/` (`generic-upper`)
- `formal/Submissions/RiscvUpper/` (`riscv-upper`)

Check it from the root of this checkout with `python3 .contract/verifier/verify.py <track> --source .`.
