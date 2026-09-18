# Proof submissions

Read `.contract/AGENTS.md` for the exact model, exports, and verification requirements.
If `.contract` is empty, run `git submodule update --init --recursive`.

A submission PR changes exactly one of `formal/Submissions/GenericLower/`,
`formal/Submissions/Lower/`, `formal/Submissions/DisclosureLower/`, or
`formal/Submissions/GenericUpper/`. Keep its `claim.txt` and exported Lean declarations consistent.
Use `python3 .contract/verifier/verify.py <track> --source .` from this repository to check the proof.

Submit proof PRs to `leanEthereum/ots.golf-submissions`. Propose changes to the model, verifier,
website, or this workspace's tooling in `leanEthereum/ots.golf-dev`.
