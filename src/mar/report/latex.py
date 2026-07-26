"""証明書 + 問題モジュールから日本語 LaTeX 論文を生成し PDF まで焼く.

依存は標準ライブラリのみ (テンプレートエンジンは ``{{KEY}}`` の単純置換)。
LaTeX は TinyTeX の ``lualatex`` を使う (jlreq + luatexja + 原ノ味フォント)。
"""

from __future__ import annotations

import re
import shutil
import subprocess
from datetime import date
from pathlib import Path

from ..certificate import Certificate
from ..problem import REPO_ROOT, Problem

TEMPLATE = Path(__file__).parent / "templates" / "paper.tex"
DEFAULT_AUTHOR = "自動研究パイプライン \\texttt{mar}（Claude Opus 5 + 検証器）"

_PLACEHOLDER = re.compile(r"\{\{([A-Z_]+)\}\}")


def render(template: str, values: dict[str, str]) -> str:
    """``{{KEY}}`` を置換する。未定義キーが残っていればエラーにする."""
    out = _PLACEHOLDER.sub(lambda m: values.get(m.group(1), m.group(0)), template)
    missing = sorted(set(_PLACEHOLDER.findall(out)))
    if missing:
        raise KeyError(f"テンプレートの未置換プレースホルダ: {missing}")
    return out


def escape(text: str) -> str:
    """プレーンテキストを LaTeX に埋め込むための最小限のエスケープ."""
    repl = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
            "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
            "^": r"\textasciicircum{}"}
    return "".join(repl.get(ch, ch) for ch in text)


def reproducibility_block(cert: Certificate, verify_cmd: str) -> str:
    p = cert.provenance
    rows = [
        ("証明書ダイジェスト", f"\\texttt{{{cert.digest()}}}"),
        ("生成日時 (UTC)", escape(p.created_at)),
        ("Python", escape(p.python)),
        ("実行環境", escape(p.platform)),
        ("リポジトリ版", f"\\texttt{{{escape(p.git_rev)}}}"),
    ]
    if p.search_seed is not None:
        rows.append(("乱数種", str(p.search_seed)))
    if p.search_seconds is not None:
        rows.append(("探索時間", f"{p.search_seconds:.1f} 秒"))
    body = " \\\\\n".join(f"{k} & {v}" for k, v in rows)
    return (
        "本稿の主張はすべて、探索器とは独立に実装された検証器によって再検査されている。"
        "次のコマンドで再現できる。\n\n"
        f"\\begin{{center}}\\texttt{{{escape(verify_cmd)}}}\\end{{center}}\n\n"
        "\\begin{center}\\begin{tabular}{ll}\\toprule\n"
        f"{body} \\\\\n\\bottomrule\\end{{tabular}}\\end{{center}}\n"
    )


def build_tex(problem: Problem, cert: Certificate, out_dir: Path,
              author: str = DEFAULT_AUTHOR) -> Path:
    sections = problem.paper_sections(cert)
    required = ("ABSTRACT", "BODY")
    for key in required:
        if key not in sections:
            raise KeyError(f"{problem.problem_id}.paper_sections に {key} がない")

    verify_cmd = f"python -m mar verify {problem.problem_id}"
    values = {
        "TITLE": sections.get("TITLE", problem.title),
        "AUTHOR": author,
        "DATE": sections.get("DATE", date.today().strftime("%Y年%m月%d日")),
        "ABSTRACT": sections["ABSTRACT"],
        "KEYWORDS": sections.get("KEYWORDS", "、".join(problem.tags)),
        "BODY": sections["BODY"],
        "REPRODUCIBILITY": sections.get(
            "REPRODUCIBILITY", reproducibility_block(cert, verify_cmd)),
        "BIBLIOGRAPHY": sections.get(
            "BIBLIOGRAPHY",
            "\n".join(r.bibitem() for r in problem.references()) or "\\item なし"),
    }
    tex = render(TEMPLATE.read_text(encoding="utf-8"), values)
    out_dir.mkdir(parents=True, exist_ok=True)
    tex_path = out_dir / "main.tex"
    tex_path.write_text(tex, encoding="utf-8")
    return tex_path


def compile_pdf(tex_path: Path, runs: int = 2) -> Path:
    """lualatex で PDF を生成する。失敗時は log の末尾を添えて例外."""
    lualatex = shutil.which("lualatex")
    if lualatex is None:
        raise RuntimeError("lualatex が見つからない (TinyTeX を PATH に入れる)")
    work = tex_path.parent
    for _ in range(runs):
        proc = subprocess.run(
            [lualatex, "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", tex_path.name],
            cwd=work, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=600,
        )
        if proc.returncode != 0:
            log = (work / (tex_path.stem + ".log"))
            tail = log.read_text(encoding="utf-8", errors="replace")[-3000:] \
                if log.exists() else proc.stdout[-3000:]
            raise RuntimeError(f"lualatex 失敗:\n{tail}")
    pdf = work / (tex_path.stem + ".pdf")
    if not pdf.exists():
        raise RuntimeError("PDF が生成されなかった")
    return pdf


def make_paper(problem: Problem, cert: Certificate,
               papers_root: Path | None = None) -> Path:
    root = papers_root or (REPO_ROOT / "papers")
    out_dir = root / problem.problem_id
    tex = build_tex(problem, cert, out_dir)
    return compile_pdf(tex)
