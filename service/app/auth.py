"""Users come from GitHub pull requests; there is no login and no token."""
from __future__ import annotations

from sqlalchemy import select
from sqlalchemy.orm import Session

from .db import User


def get_or_create_user(session: Session, login: str, github_id: int | None = None,
                       name: str | None = None, avatar_url: str | None = None) -> User:
    user = None
    if github_id is not None:
        user = session.scalars(select(User).where(User.github_id == github_id)).first()
    if user is None:
        user = session.scalars(select(User).where(User.login == login)).first()
    if user is None:
        user = User(login=login, github_id=github_id, name=name, avatar_url=avatar_url)
        session.add(user)
    else:
        user.login, user.name, user.avatar_url = login, name or user.name, avatar_url or user.avatar_url
        if github_id is not None:
            user.github_id = github_id
    session.commit()
    return user
