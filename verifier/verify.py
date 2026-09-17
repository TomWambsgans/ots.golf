#!/usr/bin/env python3
"""Verify one submission end to end, the way the hosted verifier does.

    verify.py TRACK --source PATH_OR_URL [--commit SHA] [--trusted DIR] [--lake DIR]
                    [--work DIR] [--keep] [--json]

Pipeline
  1. Take the submission root (and nothing else) from `--source` at `--commit`, or from the
     working tree of `--source` when no commit is given.
  2. Lay it over a copy of the TRUSTED tree (`--trusted`, default: this repo), so every protected
     file comes from the contract by construction.
  3. Attach a fresh clone of the warm `.lake` (`--lake`, default: <trusted>/.lake) with any
     previous build products of this track removed. The submission is compiled for the first
     time inside comparator's sandbox, which is one of comparator's stated assumptions.
  4. Policy checks: protected pin, flat root, imports, sizes, canonical claim.
  5. Render the challenge stub with the claim and run comparator under the contract's wall-clock
     limit (and, with systemd on Linux, its memory limit).
  6. Report: verified | rejected | policy_rejected | timeout | failed.

Tools come from verifier/setup_tools.sh (verifier/.tools/env.sh). On non-Linux hosts comparator
runs with its fake landrun shim: fine for development, NOT a sandbox.
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from contract import ContractError, load_challenges, read_claim, repo_root, track  # noqa: E402


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, capture_output=True, **kw)


def tools_env(root: Path) -> dict:
    env_file = root / "verifier" / ".tools" / "env.sh"
    if not env_file.is_file():
        raise ContractError("verification tools missing; run verifier/setup_tools.sh")
    env = {}
    for line in env_file.read_text().splitlines():
        if line.startswith("export ") and "=" in line:
            k, v = line[len("export "):].split("=", 1)
            env[k] = v.strip().strip('"')
    return env


def export_submission(source: str, commit: str | None, rel_root: str, dest: Path) -> str:
    """Materialize <rel_root> from the source at the commit into dest; returns the commit."""
    dest.mkdir(parents=True)
    if commit is None:
        src = Path(source)
        if not (src / rel_root).is_dir():
            raise ContractError(f"{source} has no {rel_root}")
        shutil.copytree(src / rel_root, dest / rel_root)
        return "worktree"
    with tempfile.TemporaryDirectory(prefix="ots-src-") as tmp:
        repo = Path(tmp) / "repo"
        if Path(source).is_dir():
            repo = Path(source)
        else:
            run(["git", "clone", "--filter=blob:none", "--no-checkout", source, str(repo)])
            run(["git", "-C", str(repo), "fetch", "--depth=1", "origin", commit])
        full = run(["git", "-C", str(repo), "rev-parse", "--verify", f"{commit}^{{commit}}"]).stdout.strip()
        tar = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", full, rel_root],
                             check=True, capture_output=True).stdout
        subprocess.run(["tar", "-x", "-C", str(dest)], input=tar, check=True)
        return full


def clone_tree(src: Path, dst: Path, ignore=None) -> None:
    """Copy a directory using filesystem clones where available (APFS, btrfs, xfs)."""
    if platform.system() == "Darwin":
        cmd = ["cp", "-c", "-R", str(src), str(dst)]
    else:
        cmd = ["cp", "-a", "--reflink=auto", str(src), str(dst)]
    if ignore is None:
        run(cmd)
    else:
        shutil.copytree(src, dst, ignore=ignore, symlinks=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("track")
    ap.add_argument("--source", required=True, help="git URL, or a local directory (git repo or plain tree)")
    ap.add_argument("--commit", help="commit to verify; omit to take the working tree of a local --source")
    ap.add_argument("--trusted", type=Path, help="the contract checkout (default: this repo)")
    ap.add_argument("--lake", type=Path, help="warm .lake to clone (default: <trusted>/.lake)")
    ap.add_argument("--work", type=Path, help="work directory (default: a temp dir)")
    ap.add_argument("--keep", action="store_true", help="keep the work directory")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    trusted = (a.trusted or repo_root()).resolve()
    cfg = load_challenges(trusted)
    t = track(cfg, a.track)
    lim = cfg["limits"]
    lean_root = cfg.get("lean_root", ".")
    warm_lake = (a.lake or trusted / lean_root / ".lake").resolve()
    work = (a.work or Path(tempfile.mkdtemp(prefix="ots-verify-"))).resolve()
    work.mkdir(parents=True, exist_ok=True)
    project = work / "project"
    log_path = work / "verify.log"
    result = {"track": a.track, "source": a.source, "status": "failed", "work": str(work)}
    t0 = time.time()

    def finish(status, **extra):
        result.update(status=status, duration_s=round(time.time() - t0, 1), log=str(log_path), **extra)
        if a.json:
            print(json.dumps(result, indent=2))
        else:
            print(f"{status}: track={a.track} claim={result.get('claim')} commit={result.get('commit')} "
                  f"in {result['duration_s']}s (log: {log_path})")
        if not a.keep and status in {"verified", "rejected", "policy_rejected", "timeout"}:
            shutil.rmtree(work, ignore_errors=True)
        return 0 if status == "verified" else 1

    try:
        env = tools_env(trusted)
        # 1. submission root only
        staged = work / "staged"
        result["commit"] = export_submission(a.source, a.commit, t["submission_root"], staged)
        # 2. trusted tree (without .lake and without this track's root), then overlay
        def ignore(dirpath, names):
            rel = Path(dirpath).resolve().relative_to(trusted)
            skip = set()
            for n in names:
                p = rel / n
                if str(p) in {f"{lean_root}/.lake", ".lake", ".git", "verifier/.tools", "verifier/.work",
                              t["submission_root"], t["challenge_file"]}:
                    skip.add(n)
            return skip
        shutil.copytree(trusted, project, ignore=ignore, symlinks=True)
        shutil.copytree(staged / t["submission_root"], project / t["submission_root"])
        # 3. policy (before the expensive clone)
        pin = subprocess.run([sys.executable, str(HERE / "pin_contract.py"), "check", "--root", str(project)],
                             text=True, capture_output=True)
        if pin.returncode != 0:
            log_path.write_text(pin.stdout + pin.stderr)
            return finish("failed", reason="protected files differ from the pin: " + pin.stderr.strip())
        chk = subprocess.run([sys.executable, str(HERE / "check_submission.py"), a.track, "--root", str(project), "--json"],
                             text=True, capture_output=True)
        try:
            policy = json.loads(chk.stdout)
        except ValueError:
            log_path.write_text(chk.stdout + chk.stderr)
            return finish("failed", reason="check_submission crashed: " + chk.stderr.strip())
        result["claim"] = policy.get("claim")
        if not policy["ok"]:
            log_path.write_text("\n".join(policy["errors"]) + "\n")
            return finish("policy_rejected", errors=policy["errors"])
        # 4b. warm .lake (after the cheap checks), minus this track's build products
        if not warm_lake.is_dir():
            raise ContractError(f"warm .lake missing: {warm_lake} (build the trusted tree first)")
        lake_dir = project / lean_root / ".lake"
        clone_tree(warm_lake, lake_dir)
        modpath = t["module_prefix"].replace(".", "/")
        for sub in ("build/lib/lean", "build/ir"):
            shutil.rmtree(lake_dir / sub / modpath, ignore_errors=True)
        shutil.rmtree(lake_dir / "build/lib/lean/OptimalOTS/Challenge", ignore_errors=True)
        # 5. render + comparator
        run([sys.executable, str(HERE / "render_challenge.py"), a.track, "--root", str(project)])
        cmd = ["lake", "env", env["COMPARATOR_BIN"], str(project / t["comparator_config"])]
        if platform.system() == "Linux" and shutil.which("systemd-run"):
            cmd = ["systemd-run", "--user", "--scope", "--quiet",
                   f"-p MemoryMax={lim['memory_bytes']}", "-p", "RestrictAddressFamilies=~AF_UNIX"] + cmd
        cenv = {**os.environ, "PATH": f"{Path.home()}/.elan/bin:{os.environ.get('PATH', '')}",
                "COMPARATOR_LANDRUN": env["COMPARATOR_LANDRUN"], "COMPARATOR_LEAN4EXPORT": env["COMPARATOR_LEAN4EXPORT"]}
        with log_path.open("w") as log:
            try:
                proc = subprocess.run(cmd, cwd=project / lean_root, env=cenv, stdout=log, stderr=subprocess.STDOUT,
                                      timeout=lim["wall_clock_seconds"])
            except subprocess.TimeoutExpired:
                return finish("timeout", limit_s=lim["wall_clock_seconds"])
        text = log_path.read_text(errors="replace")
        if proc.returncode == 0 and "Your solution is okay!" in text:
            return finish("verified", comparator_exit=0)
        return finish("rejected", comparator_exit=proc.returncode, tail=text[-2000:])
    except (ContractError, subprocess.CalledProcessError) as exc:
        detail = getattr(exc, "stderr", "") or str(exc)
        log_path.write_text(str(detail))
        return finish("failed", reason=str(detail)[-2000:])


if __name__ == "__main__":
    raise SystemExit(main())
