# Proof submissions

`.contract/AGENTS.md` defines the tracks, exports, rules and submission workflow; follow it. If
`.contract` is empty, run `git submodule update --init --recursive`.

A submission PR changes exactly one of these roots:

- `formal/Submissions/GenericLower/` (`generic-lower`)
- `formal/Submissions/Lower/` (`lower`)
- `formal/Submissions/DisclosureLower/` (`disclosure-lower`)
- `formal/Submissions/GenericUpper/` (`generic-upper`)
- `formal/Submissions/RiscvUpper/` (`riscv-upper`)

Check it from this repository with `python3 .contract/verifier/verify.py <track> --source .`.
