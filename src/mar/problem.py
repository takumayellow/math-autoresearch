"""問題モジュールの共通インタフェースとレジストリ.

``mar.problems`` 配下に 1 問題 1 モジュールで置く。各モジュールは ``PROBLEM``
という名前で :class:`Problem` のインスタンスを公開する。

ライフサイクル::

    survey()   先行研究ゲート: 「本当に未解決か」を人手で確認した記録
      ↓
    search()   探索。任意に重くてよい。Certificate を返す (見つからなければ None)
      ↓
    verify()   証明書 JSON だけを見る独立検証。探索の内部状態を参照してはならない
      ↓
    paper()    LaTeX 論文の材料 (定理文・本文節・図表) を返す
"""

from __future__ import annotations

import importlib
import pkgutil
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from .certificate import Certificate, VerificationReport

REPO_ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class Reference:
    """文献。論文の参考文献と「未解決性の根拠」の両方に使う."""

    key: str
    text: str
    url: str = ""

    def bibitem(self) -> str:
        tail = f" \\url{{{self.url}}}" if self.url else ""
        return f"\\bibitem{{{self.key}}} {self.text}{tail}"


@dataclass(frozen=True)
class Survey:
    """先行研究ゲートの記録.

    ``open_as_of`` は「この日付時点で未解決だと確認した」という主張であり、
    根拠 (``evidence``) が空の Survey を持つ問題は探索を実行しない。
    """

    statement: str                 # 予想・問題の正確な主張 (日本語)
    open_as_of: str                # YYYY-MM-DD
    # 根拠は自由記述 (どこで未解決と確認したか) か Reference のどちらでもよい。
    evidence: list[str | Reference] = field(default_factory=list)
    caveats: list[str] = field(default_factory=list)  # 既知の部分結果・除外例など


class Problem(ABC):
    """1 つの未解決問題に対する探索・検証・執筆の単位."""

    #: ファイル名と一致させる識別子
    problem_id: str
    #: 論文タイトル (日本語)
    title: str
    #: 分野タグ
    tags: tuple[str, ...] = ()

    @property
    @abstractmethod
    def survey(self) -> Survey:
        """先行研究ゲート。未解決であることの根拠を返す."""

    @abstractmethod
    def search(self, budget_seconds: float = 60.0,
               seed: int = 0) -> Certificate | None:
        """探索を実行し、成功したら証明書を返す."""

    @abstractmethod
    def verify(self, cert: Certificate) -> VerificationReport:
        """証明書のみから独立に検証する.

        探索器と実装を共有してはならない (共有バグが検証をすり抜けるため)。
        """

    def paper_sections(self, cert: Certificate) -> dict[str, str]:
        """LaTeX 本文の節 (キー: テンプレート内のプレースホルダ名)."""
        return {}

    def references(self) -> Iterable[Reference]:
        return self.survey.evidence


# ---------------------------------------------------------------------------
# レジストリ
# ---------------------------------------------------------------------------

def iter_problem_modules() -> list[str]:
    from . import problems
    return sorted(
        m.name for m in pkgutil.iter_modules(problems.__path__)
        if m.name.startswith("p") and not m.name.startswith("_")
    )


def load(problem_id: str) -> Problem:
    mod = importlib.import_module(f"mar.problems.{problem_id}")
    problem: Any = getattr(mod, "PROBLEM")
    if not isinstance(problem, Problem):
        raise TypeError(f"{problem_id}.PROBLEM is not a Problem instance")
    return problem


def load_all() -> list[Problem]:
    return [load(name) for name in iter_problem_modules()]
