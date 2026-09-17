#!/usr/bin/env bash
# One-shot setup of the verifier + site on a fresh Ubuntu 24.04 host (run as root once).
#
#   OTS_REPO_URL=https://github.com/<org>/<repo> OTS_DOMAIN=ots.golf bash deploy/setup-server.sh
#
# What it does: creates the unprivileged user `ots`, installs elan, Go (for landrun), uv and Caddy,
# clones the contract repository, builds the verification tools and the warm Lean build, installs
# the two systemd units (web, worker) and the Caddy site. Secrets go in /etc/ots/env afterwards.
set -euo pipefail

: "${OTS_REPO_URL:?set OTS_REPO_URL}"
: "${OTS_DOMAIN:=localhost}"
OTS_HOME=/srv/ots

apt-get update
apt-get install -y git curl build-essential python3 golang-go debian-keyring debian-archive-keyring apt-transport-https
# Caddy (TLS + reverse proxy)
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/gpg.key' | gpg --dearmor -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt' > /etc/apt/sources.list.d/caddy-stable.list
apt-get update && apt-get install -y caddy

id -u ots >/dev/null 2>&1 || useradd --system --create-home --home-dir "${OTS_HOME}" --shell /bin/bash ots
loginctl enable-linger ots   # systemd --user for the sandbox scope of the worker
mkdir -p /etc/ots
[[ -f /etc/ots/env ]] || cat > /etc/ots/env <<ENV
OTS_BASE_URL=https://${OTS_DOMAIN}
OTS_CONTRACT_REPO=$(echo "${OTS_REPO_URL}" | sed -E 's#https://github.com/([^/]+/[^/.]+).*#\1#')
GITHUB_WEBHOOK_SECRET=change-me
GITHUB_TOKEN=
OTS_DATABASE_URL=sqlite:///${OTS_HOME}/data/ots.db
OTS_DATA_DIR=${OTS_HOME}/data
ENV
chmod 600 /etc/ots/env

sudo -u ots -H bash -euo pipefail <<USER
cd "${OTS_HOME}"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="\$HOME/.elan/bin:\$HOME/.local/bin:\$PATH"
[[ -d repo/.git ]] || git clone "${OTS_REPO_URL}" repo
cd repo
verifier/setup_tools.sh
( cd formal && lake exe cache get && lake build )
python3 verifier/pin_contract.py check
( cd service && uv sync )
USER

install -m 644 "${OTS_HOME}/repo/service/deploy/ots-web.service" /etc/systemd/system/
install -m 644 "${OTS_HOME}/repo/service/deploy/ots-worker.service" /etc/systemd/system/
sed "s/{{DOMAIN}}/${OTS_DOMAIN}/" "${OTS_HOME}/repo/service/deploy/Caddyfile" > /etc/caddy/Caddyfile
systemctl daemon-reload
systemctl enable --now ots-web ots-worker caddy
echo "done. Edit /etc/ots/env (webhook secret, GitHub token), then: systemctl restart ots-web ots-worker"
