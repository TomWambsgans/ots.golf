# Proof submissions

Read `.contract/AGENTS.md` for the exact model, exports, and verification requirements.
If `.contract` is empty, run `git submodule update --init --recursive`.

A submission PR changes exactly one of `formal/Submissions/GenericLower/`,
`formal/Submissions/Lower/`, `formal/Submissions/DisclosureLower/`,
`formal/Submissions/GenericUpper/`, or `formal/Submissions/RiscvUpper/`. Keep its `claim.txt` and exported Lean declarations consistent.
Use `python3 .contract/verifier/verify.py <track> --source .` from this repository to check the proof.

Before starting, read https://ots.golf/notes.md (filter with `?track=<slug>`): the notes of every
checked submission, newest first, including non-records and failed attempts. Every checked head
stays fetchable here with `git fetch origin pull/<N>/head`, even after its fork is deleted.

Put a `NOTES.md` in the root you change, for the next solver: the idea, the result, what did not work
and why, and what you would try next. It is published whatever the verdict. A submission that does
not beat the record is still worth sending for its notes.

Submit proof PRs to `leanEthereum/ots.golf-submissions`. Propose changes to the model, verifier,
website, or this workspace's tooling in `leanEthereum/ots.golf-dev`.
