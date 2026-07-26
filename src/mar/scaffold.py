"""``mar new`` — 新しい問題モジュールの雛形を作る.

量産の律速は探索でも執筆でもなく「1 問題を立ち上げるときの定型作業」なので、
そこだけ機械化する。生成されるのは 2 ファイル:

* ``problems/pNNNN_<slug>.py``   — survey / search / verify / references
* ``problems/_pNNNN_<slug>_paper.py`` — 本文ビルダ (``build(cert)``)

雛形は**わざと動かない状態**で出てくる。``survey`` の ``evidence`` が空なので
先行研究ゲートに弾かれ、``search`` は ``NotImplementedError`` を投げる。
「空の雛形がそれっぽく走ってしまう」ほうが危険だという判断による。
"""

from __future__ import annotations

import re
from pathlib import Path

from .problem import REPO_ROOT

PROBLEM_DIR = REPO_ROOT / "src" / "mar" / "problems"

_SLUG_RE = re.compile(r"^p(\d{4})_([a-z0-9_]+)$")

_MODULE = '''"""{title}

(ここに問題の背景と、証明書の設計方針を書く。とくに「何を証人にして、
どこから先は検証器が厳密計算をやり直すのか」を最初に決めること。)
"""

from __future__ import annotations

import time

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT


class {cls}(Problem):
    problem_id = "{pid}"
    title = "{title}"
    tags = ()

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=r"(主張を正確に、日本語で)",
            open_as_of="{today}",
            # 空のままだと mar search が拒否する。未解決である根拠を書くこと。
            evidence=[],
            caveats=[],
        )

    def search(self, budget_seconds: int, seed: int) -> Certificate | None:
        started = time.time()
        raise NotImplementedError("探索を実装する")
        data = {{}}
        return Certificate(
            problem_id=self.problem_id,
            claim="(証明書が主張する内容を 1 文で)",
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=Provenance.capture(
                REPO_ROOT, seed=seed, seconds=time.time() - started, notes=""),
        )

    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        # ここでは mar.search を import しないこと (設計原則 2)。
        rep = VerificationReport(ok=True)
        rep.add("(検査項目)", False, "未実装")
        return rep

    def paper_sections(self, cert: Certificate):
        from ._{pid}_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return []


PROBLEM = {cls}()
'''

_PAPER = '''"""{pid} の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt  # noqa: F401  (graph6 等を \\texttt{{}} に包む)


def build(cert) -> dict[str, str]:
    d = cert.data  # noqa: F841

    abstract = "(要旨。証明書の数値から組み立てる)"

    body = """
\\\\section{{はじめに}}

\\\\section{{結果}}

\\\\section{{限界}}
"""
    return {{"ABSTRACT": abstract, "BODY": body}}
'''


def create(pid: str, title: str, today: str) -> list[Path]:
    """雛形を生成し、作ったファイルのパスを返す."""
    m = _SLUG_RE.match(pid)
    if not m:
        raise ValueError("problem_id は pNNNN_slug 形式 (例: p0004_foo_bar)")
    cls = "".join(part.capitalize() for part in m.group(2).split("_")) + "Problem"
    module = PROBLEM_DIR / f"{pid}.py"
    paper = PROBLEM_DIR / f"_{pid}_paper.py"
    for path in (module, paper):
        if path.exists():
            raise FileExistsError(f"すでにある: {path}")
    module.write_text(
        _MODULE.format(pid=pid, cls=cls, title=title, today=today),
        encoding="utf-8")
    paper.write_text(_PAPER.format(pid=pid), encoding="utf-8")
    return [module, paper]
