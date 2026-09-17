#!/usr/bin/env python3
"""Verify one submission end to end, the way the hosted verifier does.

    verify.py TRACK --source PATH_OR_URL [--commit SHA] [--trusted DIR] [--lake DIR]
                    [--work DIR] [--keep] [--json]

Pipeline
  1. Take the submission root (and nothing else) from `--source` at `--commit`, or from the
     working tree of `--source` when no commit is given.
  2. Lay it over a copy of the TRUSTED tree (`--trusted`, default: this repo), so every protected
     file comes from the contract by construction.
  3. Policy checks: protected pin, flat root of regular files, imports, sizes, canonical claim.
  4. Attach a fresh clone of the warm `.lake` (`--lake`, default: <trusted>/formal/.lake) with any
     previous build products of this track removed. The submission is compiled for the first
     time inside comparator's sandbox, which is one of comparator's stated assumptions.
  5. Render the challenge stub with the claim and run comparator. On Linux it runs as a transient
     systemd user service: the contract's memory and wall-clock limits on the whole process tree,
     no AF_UNIX sockets (comparator's documented requirement, since Landlock cannot block them),
     no new privileges, and an environment holding nothing but PATH, HOME and the tool paths.
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
import threading
import time
import uuid
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from contract import ContractError, load_challenges, read_claim, repo_root, track  # noqa: E402


LOG_CAP = 4 * 1024 * 1024        # bytes of comparator output kept; the rest is read and dropped


class PolicyReject(Exception):
    """The submission is refused before anything of it is copied or compiled."""


def run(cmd, **kw):
    kw.setdefault("timeout", 600)
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


def export_submission(source: str, commit: str | None, rel_root: str, dest: Path, max_files: int = 200) -> str:
    """Materialize <rel_root> from the source at the commit into dest; returns the commit."""
    dest.mkdir(parents=True)
    if commit is None:
        src = Path(source)
        if not (src / rel_root).is_dir():
            raise ContractError(f"{source} has no {rel_root}")
        shutil.copytree(src / rel_root, dest / rel_root, symlinks=True)   # a link stays a link, and is refused
        return "worktree"
    with tempfile.TemporaryDirectory(prefix="ots-src-") as tmp:
        repo = Path(tmp) / "repo"
        if Path(source).is_dir():
            repo = Path(source)
        else:
            run(["git", "clone", "--filter=blob:none", "--no-checkout", "--", source, str(repo)])
            run(["git", "-C", str(repo), "fetch", "--depth=1", "origin", commit])
        full = run(["git", "-C", str(repo), "rev-parse", "--verify", f"{commit}^{{commit}}"]).stdout.strip()
        # Only regular files may leave the repository: a symlink would be followed by the copy below,
        # outside any sandbox, and a submodule is somebody else's tree.
        tree = run(["git", "-C", str(repo), "ls-tree", "-r", "-z", full, "--", rel_root]).stdout
        entries = [e for e in tree.split("\0") if e]
        if not entries:
            raise PolicyReject(f"the commit has no {rel_root}")
        if len(entries) > max_files:
            raise PolicyReject(f"more than {max_files} files in {rel_root}")
        for e in entries:
            meta, name = e.split("\t", 1)
            mode, kind = meta.split()[:2]
            if kind != "blob" or mode not in ("100644", "100755"):
                raise PolicyReject(f"{name}: only regular files are allowed (found {kind}, mode {mode})")
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
    ap.add_argument("--lake", type=Path, help="warm .lake to clone (default: <trusted>/formal/.lake)")
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
        result["commit"] = export_submission(a.source, a.commit, t["submission_root"], staged,
                                              max_files=lim["max_files"])
        # 2. the trusted tree, allowlisted: only what a verification needs, so the copy can never
        #    recurse into work directories, tool checkouts or unrelated files
        def skip(names_to_skip):
            return lambda dirpath, names: {n for n in names if n in names_to_skip or n == "__pycache__"}
        project.mkdir(parents=True)
        shutil.copyfile(trusted / "challenges.json", project / "challenges.json")
        shutil.copytree(trusted / "verifier", project / "verifier", ignore=skip({".tools", ".work"}))
        root_rel = Path(t["submission_root"]).relative_to(lean_root)
        chal_rel = Path(t["challenge_file"]).relative_to(lean_root)
        def skip_lean(dirpath, names):
            rel = Path(dirpath).resolve().relative_to((trusted / lean_root).resolve())
            return {n for n in names if n == ".lake" or (rel / n) in {root_rel, chal_rel}}
        shutil.copytree(trusted / lean_root, project / lean_root, ignore=skip_lean, symlinks=True)
        shutil.copytree(staged / t["submission_root"], project / t["submission_root"], symlinks=True)
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
        home = str(Path.home())
        path = f"{home}/.elan/bin:{os.environ.get('PATH', '/usr/local/bin:/usr/bin:/bin')}"
        # Nothing of the caller's environment reaches comparator or the code it builds: the worker's
        # carries the GitHub token and the webhook secret.
        sandbox_env = {"PATH": path, "HOME": home, "LANG": "C.UTF-8",
                       "COMPARATOR_LANDRUN": env["COMPARATOR_LANDRUN"],
                       "COMPARATOR_LEAN4EXPORT": env["COMPARATOR_LEAN4EXPORT"]}
        lake = shutil.which("lake", path=path) or "lake"
        cmd = [lake, "env", env["COMPARATOR_BIN"], str(project / t["comparator_config"])]
        cenv, unit = dict(sandbox_env), None
        if platform.system() == "Linux" and shutil.which("systemd-run"):
            lsm = Path("/sys/kernel/security/lsm")
            if not (lsm.is_file() and "landlock" in lsm.read_text()):
                return finish("failed", reason="Landlock is not enabled on this kernel: refusing to build untrusted code")
            # A transient user SERVICE, not a scope: only a service can carry RestrictAddressFamilies,
            # which comparator requires because Landlock cannot block unix sockets, and only a service
            # is killed as a whole cgroup when the time is up. Under a system service there is no
            # session environment; the user's manager (kept alive by `loginctl enable-linger`)
            # listens under /run/user/<uid>.
            unit = f"ots-verify-{uuid.uuid4().hex[:12]}"
            props = [f"MemoryMax={lim['memory_bytes']}", "MemorySwapMax=0",
                     f"RuntimeMaxSec={lim['wall_clock_seconds']}", "KillMode=control-group",
                     "RestrictAddressFamilies=~AF_UNIX", "NoNewPrivileges=yes"]
            cmd = (["systemd-run", "--user", "--wait", "--collect", "--pipe", "--quiet", f"--unit={unit}",
                    f"--working-directory={project / lean_root}"]
                   + [x for p in props for x in ("-p", p)]
                   + [x for k, v in sandbox_env.items() for x in ("-E", f"{k}={v}")] + ["--"] + cmd)
            runtime = os.environ.get("XDG_RUNTIME_DIR", f"/run/user/{os.getuid()}")
            cenv = {"PATH": path, "HOME": home, "XDG_RUNTIME_DIR": runtime,
                    "DBUS_SESSION_BUS_ADDRESS": os.environ.get("DBUS_SESSION_BUS_ADDRESS", f"unix:path={runtime}/bus")}
        elif "TMPDIR" in os.environ:
            cenv["TMPDIR"] = os.environ["TMPDIR"]

        def stop_unit():
            if unit:
                subprocess.run(["systemctl", "--user", "kill", "--signal=KILL", unit], env=cenv,
                               capture_output=True, timeout=30)

        started = time.time()
        proc = subprocess.Popen(cmd, cwd=project / lean_root, env=cenv, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, start_new_session=True)

        def pump():                                   # keep the head of the output, drain the rest
            kept = 0
            with log_path.open("wb") as log:
                for chunk in iter(lambda: proc.stdout.read(65536), b""):
                    if kept < LOG_CAP:
                        log.write(chunk[:LOG_CAP - kept])
                        kept += len(chunk)
                        if kept >= LOG_CAP:
                            log.write(b"\n[output truncated]\n")

        reader = threading.Thread(target=pump, daemon=True)
        reader.start()
        try:
            proc.wait(timeout=lim["wall_clock_seconds"] + 60)
        except subprocess.TimeoutExpired:
            stop_unit()
            try:
                os.killpg(proc.pid, 9)
            except OSError:
                pass
            proc.wait()
            reader.join(10)
            return finish("timeout", limit_s=lim["wall_clock_seconds"])
        reader.join(30)
        if proc.returncode != 0 and time.time() - started >= lim["wall_clock_seconds"] - 1:
            stop_unit()                               # RuntimeMaxSec already killed the tree
            return finish("timeout", limit_s=lim["wall_clock_seconds"])
        text = log_path.read_text(errors="replace")
        if proc.returncode == 0 and "Your solution is okay!" in text:
            return finish("verified", comparator_exit=0)
        return finish("rejected", comparator_exit=proc.returncode, tail=text[-2000:])
    except PolicyReject as exc:
        log_path.write_text(str(exc) + "\n")
        return finish("policy_rejected", errors=[str(exc)])
    except (ContractError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        detail = getattr(exc, "stderr", "") or str(exc)
        log_path.write_text(str(detail))
        return finish("failed", reason=str(detail)[-2000:])


if __name__ == "__main__":
    raise SystemExit(main())
