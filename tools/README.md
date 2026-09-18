# Numerical tools

These scripts explore constructions and attack arithmetic. A positive result is not a Lean proof.

`python3 tools/tune_lower_bound.py --method words --claims 93,94` checks the whole-word attack
with exact integers and fractions. Use `--method patterns --claims 18` for the unrestricted DAG
certificate. `--method disclosure --claims 80` reproduces the historical bounded-origin estimate.
The entropy mode is conditional research; its missing hypotheses are false in the bare model.

`search_forest.py` needs NumPy. An isolated environment keeps it out of the service dependencies:

```sh
uv venv .venv-tools
uv pip install --python .venv-tools/bin/python numpy
.venv-tools/bin/python tools/search_forest.py --check 14,3,3,7 --overhead 16
.venv-tools/bin/python -m unittest discover -s tools/tests -v
```

The checked shape has key-generation cost 912 and reconstruction cost 105, plus one compression
for the message-and-nonce index. `--overhead` adds explicit bits to each graph hash input only;
it never changes that index query. Float arithmetic finds candidates; Python integers recount
the selected candidate exactly. This counts a disclosure family and does not prove security.

## Repository regression checks

After preparing the service environment, run:

```sh
python3 tools/check_repo.py --numerics-python .venv-tools/bin/python --formal --paper
```

Node.js is used only for static JavaScript syntax checks (`--node /path/to/node` overrides PATH).
`--official` adds every configured official certificate pipeline. These commands use the existing warm
Lean/tool caches and do not install packages, refresh demos, push, or deploy. Browser checks use
`service/browser_check.py` against the seeded local preview. Linux sandbox acceptance must run
on the actual deployment host with `verifier/check_linux_sandbox.py`; a macOS pass cannot replace it.
