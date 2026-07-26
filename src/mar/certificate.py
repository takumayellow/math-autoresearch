"""有限証明書 (finite certificate) の表現と入出力.

設計原則
--------
本フレームワークにおける「結果」とは、常に次の 2 つの組である:

1. **対象 (object)**: 反例・構成・データ列そのもの。有理数など厳密に表現可能な
   値のみを許し、浮動小数点数は証明書に入れない。
2. **検証手続き (verifier)**: 証明書 JSON *だけ* を入力として受け取り、探索側の
   状態に一切依存せずに真偽を判定する関数。

探索器がどれほど複雑でも、検証器が単純かつ独立であれば結果は信用できる。これは
2026 年のヤコビアン予想の反例 (定数ヤコビアンと明示的な非単射性という 2 つの有限
証明書) が示した構図をそのまま採用したものである。
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .osinfo import os_label


def _git_rev(repo_root: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10,
        )
        return out.stdout.strip() or "uncommitted"
    except Exception:
        return "unknown"


@dataclass(frozen=True)
class Provenance:
    """再現に必要な最小限のメタデータ."""

    created_at: str
    python: str
    platform: str
    git_rev: str
    search_seed: int | None = None
    search_seconds: float | None = None
    notes: str = ""

    @staticmethod
    def capture(repo_root: Path, seed: int | None = None,
                seconds: float | None = None, notes: str = "") -> "Provenance":
        return Provenance(
            created_at=datetime.now(timezone.utc).isoformat(timespec="seconds"),
            python=sys.version.split()[0],
            platform=os_label(),
            git_rev=_git_rev(repo_root),
            search_seed=seed,
            search_seconds=seconds,
            notes=notes,
        )


@dataclass(frozen=True)
class Certificate:
    """1 つの主張とその有限証拠.

    Attributes
    ----------
    problem_id:
        ``problems/`` 配下の問題モジュール ID (例 ``"p0002_ags_conjecture"``)。
    claim:
        人間可読な主張文 (日本語 1 文)。論文の定理文にそのまま使う。
    kind:
        ``"counterexample"`` | ``"construction"`` | ``"exhaustive"`` | ``"data"``
    data:
        JSON 化可能な証拠本体。分数は ``"p/q"`` 形式の文字列で持つ。
    provenance:
        再現メタデータ。
    """

    problem_id: str
    claim: str
    kind: str
    data: dict[str, Any]
    provenance: Provenance

    def digest(self) -> str:
        """証拠本体のみのハッシュ (メタデータを除く同一性判定用)."""
        blob = json.dumps({"problem_id": self.problem_id, "kind": self.kind,
                           "data": self.data}, sort_keys=True, ensure_ascii=False)
        return hashlib.sha256(blob.encode("utf-8")).hexdigest()[:16]

    def to_json(self) -> str:
        payload = asdict(self)
        payload["digest"] = self.digest()
        return json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)

    def save(self, path: Path) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(self.to_json(), encoding="utf-8")
        return path

    @staticmethod
    def load(path: Path) -> "Certificate":
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
        payload.pop("digest", None)
        prov = Provenance(**payload.pop("provenance"))
        return Certificate(provenance=prov, **payload)


@dataclass
class VerificationReport:
    """検証結果. ``ok`` が False の証明書は決して論文化しない."""

    ok: bool
    checks: list[tuple[str, bool, str]] = field(default_factory=list)

    def add(self, name: str, passed: bool, detail: str = "") -> None:
        self.checks.append((name, passed, detail))
        self.ok = self.ok and passed

    def render(self) -> str:
        lines = []
        for name, passed, detail in self.checks:
            mark = "PASS" if passed else "FAIL"
            lines.append(f"  [{mark}] {name}" + (f" — {detail}" if detail else ""))
        lines.append(f"  => {'ALL PASS' if self.ok else 'FAILED'}")
        return "\n".join(lines)
