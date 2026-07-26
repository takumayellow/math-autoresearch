"""検証結果の記録 (verification record).

``verify`` は元データを丸ごと走査するので、族が大きい問題では 1 回に数十分
かかる。検証が終わったら、**何を検証したか**を
``data/verifications/`` に残しておく: 証明書のダイジェスト、検証器コードの
ハッシュ、各検査項目の結果、所要時間。

記録は履歴であって保証ではない。``paper`` は既定では記録を見ずに検証を
やり直す (README の原則 4)。``--use-record`` を明示したときだけ、

* 証明書のダイジェストが一致し、
* 検証器コードのハッシュも一致し、
* 全項目 PASS

の 3 条件が揃った記録を再利用する。証明書を 1 バイト書き換えても、
``mar.checkgraph`` を書き換えても記録は無効になる。ただし記録そのものは
ただの JSON なので、**手で書けば偽造できる**。信用の根拠はあくまで
「誰でも `mar verify` を走らせ直せる」ことの方であって、この記録ではない。
"""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

from .certificate import Certificate, VerificationReport
from .osinfo import os_label
from .problem import REPO_ROOT

RECORD_DIR = REPO_ROOT / "data" / "verifications"
#: 検証の中身を決めるコード。1 バイトでも変われば過去の記録は使わない。
VERIFIER_SOURCES = ("checkgraph.py", "exact.py", "certificate.py")


def record_path(problem_id: str) -> Path:
    return RECORD_DIR / f"{problem_id}.json"


def verifier_hash(problem_id: str) -> str:
    """検証器コード (共通部分 + 当該問題モジュール) のハッシュ."""
    root = Path(__file__).resolve().parent
    digest = hashlib.sha256()
    paths = [root / name for name in VERIFIER_SOURCES]
    paths.append(root / "problems" / f"{problem_id}.py")
    for path in paths:
        digest.update(path.name.encode("utf-8"))
        digest.update(path.read_bytes() if path.exists() else b"")
    return digest.hexdigest()[:16]


def save_record(cert: Certificate, report: VerificationReport,
                seconds: float) -> Path:
    """検証結果を証明書のダイジェストつきで保存する."""
    payload = {
        "problem_id": cert.problem_id,
        "certificate_digest": cert.digest(),
        "verifier_hash": verifier_hash(cert.problem_id),
        "ok": report.ok,
        "checks": [{"name": name, "passed": passed, "detail": detail}
                   for name, passed, detail in report.checks],
        "verified_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "seconds": round(seconds, 1),
        "python": sys.version.split()[0],
        "platform": os_label(),
    }
    path = record_path(cert.problem_id)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2,
                               sort_keys=True), encoding="utf-8")
    return path


def load_record(cert: Certificate) -> dict | None:
    """この証明書とこの検証器コードに対する PASS 記録があれば返す.

    証明書・検証器のどちらかが変わっていれば ``None`` (= 検証をやり直す)。
    """
    path = record_path(cert.problem_id)
    if not path.exists():
        return None
    try:
        rec = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not rec.get("ok"):
        return None
    if rec.get("certificate_digest") != cert.digest():
        return None
    if rec.get("verifier_hash") != verifier_hash(cert.problem_id):
        return None
    return rec


def render_record(rec: dict) -> str:
    lines = [f"  [PASS] {c['name']}" + (f" — {c['detail']}" if c.get("detail") else "")
             for c in rec.get("checks", [])]
    lines.append(f"  => ALL PASS (記録: {rec.get('verified_at')}, "
                 f"{rec.get('seconds')} 秒, "
                 f"verifier={rec.get('verifier_hash')})")
    return "\n".join(lines)
