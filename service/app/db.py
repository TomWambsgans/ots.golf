"""Database: users and submissions, in SQLite (WAL) under the data directory."""
from __future__ import annotations

import json
import uuid
from datetime import datetime, timezone

from sqlalchemy import Boolean, DateTime, Float, ForeignKey, Integer, String, Text, create_engine, event
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship, sessionmaker

from .config import settings


def utcnow() -> datetime:
    """Naive UTC, which is what every backend stores faithfully."""
    return datetime.now(timezone.utc).replace(tzinfo=None)


class Base(DeclarativeBase):
    pass


class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(primary_key=True)
    github_id: Mapped[int | None] = mapped_column(Integer, unique=True, nullable=True)
    login: Mapped[str] = mapped_column(String(80), unique=True)
    name: Mapped[str | None] = mapped_column(String(200), nullable=True)
    avatar_url: Mapped[str | None] = mapped_column(String(400), nullable=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)
    submissions: Mapped[list["Submission"]] = relationship(back_populates="user")



class Submission(Base):
    __tablename__ = "submissions"
    id: Mapped[str] = mapped_column(String(32), primary_key=True, default=lambda: uuid.uuid4().hex)
    track: Mapped[str] = mapped_column(String(16), index=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id"), index=True)
    source_repo: Mapped[str] = mapped_column(String(400))
    commit: Mapped[str] = mapped_column(String(64))
    claim: Mapped[int | None] = mapped_column(Integer, nullable=True)
    status: Mapped[str] = mapped_column(String(20), default="pending", index=True)
    is_record: Mapped[bool] = mapped_column(Boolean, default=False)
    record_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    baseline: Mapped[bool] = mapped_column(Boolean, default=False)
    assisted_by: Mapped[str | None] = mapped_column(String(120), nullable=True)
    description: Mapped[str | None] = mapped_column(Text, nullable=True)
    co_authors: Mapped[str] = mapped_column(Text, default="[]")
    pr_number: Mapped[int | None] = mapped_column(Integer, nullable=True)
    pr_url: Mapped[str | None] = mapped_column(String(400), nullable=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow, index=True)
    started_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    finished_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    duration_s: Mapped[float | None] = mapped_column(Float, nullable=True)
    detail: Mapped[str] = mapped_column(Text, default="{}")
    log_path: Mapped[str | None] = mapped_column(String(400), nullable=True)
    user: Mapped[User] = relationship(back_populates="submissions")

    @property
    def co_authors_list(self) -> list[str]:
        try:
            return list(json.loads(self.co_authors or "[]"))
        except ValueError:
            return []

    @property
    def detail_dict(self) -> dict:
        try:
            return dict(json.loads(self.detail or "{}"))
        except ValueError:
            return {}

    @property
    def commit_url(self) -> str | None:
        if self.source_repo.startswith("https://github.com/"):
            return f"{self.source_repo.removesuffix('.git')}/commit/{self.commit}"
        return None


is_sqlite = settings.database_url.startswith("sqlite")
engine = create_engine(settings.database_url, connect_args={"check_same_thread": False} if is_sqlite else {})
if is_sqlite:
    @event.listens_for(engine, "connect")
    def _sqlite_pragmas(dbapi_conn, _):
        cur = dbapi_conn.cursor()
        cur.execute("PRAGMA journal_mode=WAL")
        cur.execute("PRAGMA busy_timeout=5000")
        cur.close()

SessionLocal = sessionmaker(engine, expire_on_commit=False)


def init_db() -> None:
    Base.metadata.create_all(engine)


def get_session():
    with SessionLocal() as session:
        yield session
