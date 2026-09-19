# Proof submissions

Follow `.contract/AGENTS.md`: it is the precise specification of the tracks, exports, root rules
and submission workflow. If `.contract` is empty, run `git submodule update --init --recursive`.

| Slug | Submission root |
|---|---|
| `upper-compressions` | `formal/Submissions/UpperCompressions/` |
| `upper-riscv` | `formal/Submissions/UpperRiscv/` |
| `lower-generality-1` | `formal/Submissions/LowerGenerality1/` |
| `lower-generality-2` | `formal/Submissions/LowerGenerality2/` |
| `lower-generality-3` | `formal/Submissions/LowerGenerality3/` |

Check a root from the root of this checkout with
`python3 .contract/verifier/verify.py <slug> --source .`.
