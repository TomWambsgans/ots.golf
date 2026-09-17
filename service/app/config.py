"""Settings from the environment. Everything has a localhost default."""
from __future__ import annotations

import os
import secrets
from dataclasses import dataclass
from pathlib import Path

SERVICE_DIR = Path(__file__).resolve().parent.parent
DEFAULT_REPO_ROOT = SERVICE_DIR.parent


def _secret(data_dir: Path) -> str:
    env = os.environ.get("OTS_SECRET_KEY")
    if env:
        return env
    p = data_dir / "secret_key"
    if p.is_file():
        return p.read_text().strip()
    s = secrets.token_urlsafe(48)
    p.write_text(s)
    os.chmod(p, 0o600)
    return s


@dataclass
class Settings:
    repo_root: Path = Path(os.environ.get("OTS_REPO_ROOT", str(DEFAULT_REPO_ROOT))).resolve()
    data_dir: Path = Path(os.environ.get("OTS_DATA_DIR", str(SERVICE_DIR / "data"))).resolve()
    base_url: str = os.environ.get("OTS_BASE_URL", "http://localhost:8000").rstrip("/")
    github_webhook_secret: str = os.environ.get("GITHUB_WEBHOOK_SECRET", "")
    github_token: str = os.environ.get("GITHUB_TOKEN", "")
    contract_repo: str = os.environ.get("OTS_CONTRACT_REPO", "")  # owner/name of the public repo
    queue_cap: int = int(os.environ.get("OTS_QUEUE_CAP", "20"))
    max_inflight_per_user: int = int(os.environ.get("OTS_MAX_INFLIGHT_PER_USER", "2"))
    database_url: str = ""
    secret_key: str = ""

    def __post_init__(self) -> None:
        self.data_dir.mkdir(parents=True, exist_ok=True)
        (self.data_dir / "logs").mkdir(exist_ok=True)
        (self.data_dir / "work").mkdir(exist_ok=True)
        self.database_url = os.environ.get("OTS_DATABASE_URL", f"sqlite:///{self.data_dir / 'ots.db'}")
        self.secret_key = _secret(self.data_dir)


settings = Settings()
