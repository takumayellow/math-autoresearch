"""X (Twitter) への投稿。studyai の ``tools/x_poster`` と同じ資格情報を使う.

資格情報は **リポジトリに置かない**。次の順に ``.env`` 形式のファイルを探し、
最初に見つかったものを読む (環境変数が既にあればそれが最優先):

1. ``$MAR_X_ENV`` が指すファイル
2. ``<repo>/.env.local``
3. ``~/dev/studyai/.env.local``
4. ``~/dev/studyai/tools/x_poster/.env``

``$MAR_X_ENV`` でリポジトリ内のファイルを指すなら、``.gitignore`` が拾える
``.env*`` という名前にする。それ以外の名前だと追跡対象になって漏れる。

必要なキーは studyai と同じ 4 つ::

    TWITTER_API_KEY / TWITTER_API_SECRET
    TWITTER_ACCESS_TOKEN / TWITTER_ACCESS_TOKEN_SECRET

投稿は API v2 (``tweepy.Client.create_tweet``)、画像添付だけ v1.1 の
``media_upload`` を使う (v2 に画像アップロードの口がないため)。
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

from ..problem import REPO_ROOT

ENV_KEYS = ("TWITTER_API_KEY", "TWITTER_API_SECRET",
            "TWITTER_ACCESS_TOKEN", "TWITTER_ACCESS_TOKEN_SECRET")

STUDYAI = Path.home() / "dev" / "studyai"


def env_candidates() -> list[Path]:
    paths = []
    override = os.environ.get("MAR_X_ENV")
    if override:
        paths.append(Path(override))
    paths += [REPO_ROOT / ".env.local",
              STUDYAI / ".env.local",
              STUDYAI / "tools" / "x_poster" / ".env"]
    return paths


def _parse_env(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        out[key.strip()] = value.strip().strip('"').strip("'")
    return out


@dataclass(frozen=True)
class Credentials:
    api_key: str
    api_secret: str
    access_token: str
    access_token_secret: str
    source: str


class CredentialsError(RuntimeError):
    """4 つのキーが揃わない."""


def load_credentials() -> Credentials:
    values = {k: os.environ.get(k, "") for k in ENV_KEYS}
    source = "環境変数"
    if not all(values.values()):
        for path in env_candidates():
            if not path.exists():
                continue
            found = _parse_env(path)
            for key in ENV_KEYS:
                values[key] = values[key] or found.get(key, "")
            if all(values.values()):
                source = str(path)
                break
    missing = [k for k in ENV_KEYS if not values[k]]
    if missing:
        tried = "\n  ".join(str(p) for p in env_candidates())
        raise CredentialsError(
            "X の資格情報が足りない: " + ", ".join(missing)
            + "\n探した場所:\n  " + tried)
    return Credentials(values["TWITTER_API_KEY"], values["TWITTER_API_SECRET"],
                       values["TWITTER_ACCESS_TOKEN"],
                       values["TWITTER_ACCESS_TOKEN_SECRET"], source)


def post_thread(texts: list[str], image: Path | None = None) -> dict:
    """1 通目 + 続き (返信) を投稿する。戻り値は ``{"id", "url", "ids"}``.

    ``id`` / ``url`` は 1 通目のもの (スレッドの入口)。
    """
    if not texts:
        raise ValueError("投稿する本文がない")
    try:
        import tweepy  # 遅延 import: 投稿しないときは不要
    except ImportError as exc:  # pragma: no cover - 環境依存
        raise RuntimeError(
            "tweepy が入っていない。`pip install tweepy` を実行する。") from exc

    creds = load_credentials()
    media_ids = None
    if image is not None:
        auth = tweepy.OAuth1UserHandler(
            creds.api_key, creds.api_secret,
            creds.access_token, creds.access_token_secret)
        media = tweepy.API(auth).media_upload(filename=str(image))
        media_ids = [media.media_id]

    client = tweepy.Client(
        consumer_key=creds.api_key, consumer_secret=creds.api_secret,
        access_token=creds.access_token,
        access_token_secret=creds.access_token_secret)
    ids: list[str] = []
    for i, text in enumerate(texts):
        resp = client.create_tweet(
            text=text,
            media_ids=media_ids if i == 0 else None,
            in_reply_to_tweet_id=ids[-1] if ids else None)
        ids.append(str(resp.data["id"]))
    return {"id": ids[0], "ids": ids,
            "url": f"https://x.com/i/web/status/{ids[0]}"}
