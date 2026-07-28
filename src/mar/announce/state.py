"""投稿台帳: 「どの成果を、どの証明書の版で投稿したか」.

鍵は ``(problem_id, certificate_digest)``。証明書が変わらない限り再投稿
しない。逆に、探索をやり直して結果が変われば digest が変わるので、同じ
問題でも「更新版」として投稿できる。
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path

from ..problem import REPO_ROOT

LEDGER_PATH = REPO_ROOT / "data" / "announce" / "posted.json"


@dataclass(frozen=True)
class PostRecord:
    problem_id: str
    certificate_digest: str
    posted_at: str
    text: str
    tweet_id: str = ""
    tweet_url: str = ""
    #: スレッドで投稿した場合の全ツイート ID (1 通目を含む)
    tweet_ids: tuple[str, ...] = ()
    dry_run: bool = False


class LedgerError(RuntimeError):
    """台帳が読めない。空とみなすと全件を再投稿してしまうので必ず落とす."""


def load_ledger(path: Path = LEDGER_PATH) -> list[PostRecord]:
    """台帳を読む。存在しなければ空、\
壊れていれば :class:`LedgerError`.

    壊れた台帳を「投稿記録なし」と読み替えるのが最悪の失敗 (過去に投稿した
    成果をまとめて再投稿する) なので、ここでは黙って握りつぶさない。
    """
    if not path.exists():
        return []
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LedgerError(f"台帳が読めない: {path}: {exc}") from exc
    if not isinstance(raw, dict) or not isinstance(raw.get("posts", []), list):
        raise LedgerError(f"台帳の形式が想定と違う: {path}")
    known = set(PostRecord.__dataclass_fields__)
    out = []
    for i, item in enumerate(raw.get("posts", [])):
        try:
            out.append(PostRecord(**{k: v for k, v in item.items()
                                     if k in known}))
        except (TypeError, AttributeError) as exc:
            raise LedgerError(f"台帳 {path} の {i} 番目の記録が壊れている: "
                              f"{exc}") from exc
    return out


def find(problem_id: str, digest: str,
         path: Path = LEDGER_PATH) -> PostRecord | None:
    """この問題のこの証明書版で、実投稿 (dry-run でない) の記録を返す."""
    for rec in load_ledger(path):
        if (rec.problem_id == problem_id
                and rec.certificate_digest == digest and not rec.dry_run):
            return rec
    return None


def append(record: PostRecord, path: Path = LEDGER_PATH) -> Path:
    posts = [asdict(r) for r in load_ledger(path)]
    posts.append(asdict(record))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"posts": posts}, ensure_ascii=False, indent=2),
                    encoding="utf-8")
    return path


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")
