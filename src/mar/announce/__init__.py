"""成果を X に投稿するための組み立て.

「問題ごと」ではなく「**成果が出た問題ごと**」に投稿する。ここでの成果と
は、次の 3 つが揃っているものを指す:

1. 証明書 (``data/certificates/<id>.json``) がある
2. **その証明書と、今の検証器コードに対する** PASS 記録がある
   (:func:`mar.verification.load_record`。証明書を 1 バイト変えても、
   検証器を書き換えても、記録は無効になる)
3. 論文 PDF (``papers/<id>/main.pdf``) がビルドされている

したがって、探索し直して未検証の問題や、検証が落ちた問題は自動的に投稿
対象から外れる。投稿文の数値はすべて証明書の ``claim`` から引く
(:mod:`mar.announce.compose`)。
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from ..certificate import Certificate
from ..problem import REPO_ROOT, iter_problem_modules
from ..verification import load_record
from . import state
from .compose import compose, weighted_length
from .highlights import highlight

REPO_URL = "https://github.com/takumayellow/math-autoresearch"
CERT_DIR = REPO_ROOT / "data" / "certificates"
PAPER_DIR = REPO_ROOT / "papers"


@dataclass(frozen=True)
class Post:
    problem_id: str
    certificate_digest: str
    text: str
    #: 1 通目に入りきらなかった主張の続き (スレッドの返信)
    replies: tuple[str, ...]
    pdf_url: str
    image: Path | None
    already_posted: state.PostRecord | None

    @property
    def weighted_length(self) -> int:
        return weighted_length(self.text)

    def all_texts(self) -> list[str]:
        return [self.text, *self.replies]


def pdf_path(problem_id: str) -> Path:
    return PAPER_DIR / problem_id / "main.pdf"


def pdf_url(problem_id: str) -> str:
    return f"{REPO_URL}/blob/main/papers/{problem_id}/main.pdf"


def preview_image(problem_id: str) -> Path | None:
    """論文 1 ページ目の PNG (あれば投稿に添える)."""
    path = PAPER_DIR / problem_id / "preview" / "page01.png"
    return path if path.exists() else None


def readiness(problem_id: str) -> tuple[bool, str]:
    """投稿対象かどうかと、対象外ならその理由."""
    cert_file = CERT_DIR / f"{problem_id}.json"
    if not cert_file.exists():
        return False, "証明書がない (未探索)"
    cert = Certificate.load(cert_file)
    if load_record(cert) is None:
        return False, "今の証明書・検証器に対する PASS 記録がない (要 verify)"
    if not pdf_path(problem_id).exists():
        return False, "論文 PDF が未ビルド"
    return True, ""


def ready_problems() -> list[str]:
    return [pid for pid in iter_problem_modules() if readiness(pid)[0]]


def build_post(problem_id: str) -> Post:
    """投稿文を組み立てる (検証が通っていない問題は作らない)."""
    ok, why = readiness(problem_id)
    if not ok:
        raise ValueError(f"{problem_id}: {why}")
    cert = Certificate.load(CERT_DIR / f"{problem_id}.json")
    hl = highlight(problem_id)
    url = pdf_url(problem_id)
    text, replies = compose(hl.headline, cert.claim, url, hl.tags)
    return Post(
        problem_id=problem_id,
        certificate_digest=cert.digest(),
        text=text,
        replies=tuple(replies),
        pdf_url=url,
        image=preview_image(problem_id),
        already_posted=state.find(problem_id, cert.digest()),
    )


def pending_posts() -> list[Post]:
    """検証が通っていて、まだ (この証明書版では) 投稿していないもの."""
    posts = [build_post(pid) for pid in ready_problems()]
    return [p for p in posts if p.already_posted is None]
