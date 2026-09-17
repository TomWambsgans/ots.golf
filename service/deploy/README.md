# Deploying on a server

Target: one Linux box (Ubuntu 24.04, 8+ cores, 32 GB or more: the contract caps a verification at
24 GiB). NVMe on a filesystem with reflinks, such as btrfs or xfs, makes each verification's clone of
the warm build instant; on ext4 it is an 8 GB copy, which works but takes a minute.

1. `OTS_REPO_URL=https://github.com/<org>/<repo> OTS_DOMAIN=ots.golf bash deploy/setup-server.sh`
   as root. It creates the `ots` user, installs elan, Go, uv and Caddy, clones the repository, builds
   comparator, lean4export and landrun, warms Mathlib, VCVio and the baselines, and installs the
   `ots-web`, `ots-worker` and `caddy` units.
2. `/etc/ots/secrets.env` (root only) already holds a generated webhook secret; add a fine-grained
   GitHub token limited to this repository (commit statuses and pull requests, read and write, no
   contents write), then `systemctl restart ots-web ots-worker`. Untrusted Lean code runs as the
   `ots` user with read access to the filesystem, so this file must stay `root:root 0600`; the
   non-secret settings live in `/etc/ots/public.env`.
3. On GitHub, add a webhook on the contract repository: payload URL `https://<domain>/webhooks/github`,
   content type JSON, the same secret, event "Pull requests".
4. Queue the baselines once, with the services' settings:
   ```sh
   sudo -u ots -H bash -c 'set -a; . /etc/ots/public.env; set +a; cd /srv/ots/repo/service &&
     OTS_REPO_ROOT=/srv/ots/repo .venv/bin/python -m app.queue lower --baseline &&
     OTS_REPO_ROOT=/srv/ots/repo .venv/bin/python -m app.queue upper --baseline'
   ```
   Without the settings the command would write to a database of its own under `service/data`,
   which the worker never reads.

The sandbox chain is comparator → landrun (Landlock: read-only tree, writable `.lake` only, no
network) inside a transient service of the `ots` user's manager (`systemd-run --user --wait`) that
carries the contract's memory and time limits on the whole process tree, forbids unix sockets
(comparator's documented requirement) and new privileges, and gets an environment with nothing but
PATH, HOME and the tool paths; `loginctl enable-linger` keeps that manager available. The trusted tree is never compiled with
a submission in place: each verification works on a copy.

Backups: `data/ots.db` and `data/logs/` are the whole state; the machine is otherwise rebuildable
from this script.
