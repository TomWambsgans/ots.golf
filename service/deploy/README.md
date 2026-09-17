# Deploying on a server

Target: one Linux box (Ubuntu 24.04, 8+ cores, 32 GB or more: the contract caps a verification at
24 GiB). NVMe on a filesystem with reflinks, such as btrfs or xfs, makes each verification's clone of
the warm build instant; on ext4 it is an 8 GB copy, which works but takes a minute.

1. `OTS_REPO_URL=https://github.com/<org>/<repo> OTS_DOMAIN=ots.golf bash deploy/setup-server.sh`
   as root. It creates the `ots` user, installs elan, Go, uv and Caddy, clones the repository, builds
   comparator, lean4export and landrun, warms Mathlib, VCVio and the baselines, and installs the
   `ots-web`, `ots-worker` and `caddy` units.
2. Put the GitHub webhook secret and a token that may set commit statuses and comment on pull
   requests in `/etc/ots/env`, then `systemctl restart ots-web ots-worker`.
3. On GitHub, add a webhook on the contract repository: payload URL `https://<domain>/webhooks/github`,
   content type JSON, the same secret, event "Pull requests".
4. Queue the baselines once: `sudo -u ots /srv/ots/repo/service/.venv/bin/python -m app.queue lower --baseline`
   (and `upper` once its proof is in the repository).

The sandbox chain is comparator → landrun (Landlock: read-only tree, writable `.lake` only, no
network) inside a `systemd-run --user --scope` with the contract's memory cap; the worker's
`loginctl enable-linger` makes the user manager available. The trusted tree is never compiled with
a submission in place: each verification works on a copy.

Backups: `data/ots.db` and `data/logs/` are the whole state; the machine is otherwise rebuildable
from this script.
