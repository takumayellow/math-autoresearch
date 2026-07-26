"""LaTeX への文字列埋め込み.

graph6 は ASCII 63--126 をそのまま使う符号なので、``\\``, ``{``, ``}``,
``~``, ``^``, ``_`` といった LaTeX の特殊文字が普通に現れる。
これをそのまま ``\\texttt{...}`` に入れると組版が壊れる (実際に $n = 18$ の
立方体グラフの graph6 で ``}`` が \\texttt を閉じてしまい、コンパイルが
失敗した)。本モジュールはその変換を 1 か所に集める。
"""

from __future__ import annotations

BACKSLASH = chr(92)

#: LaTeX の特殊文字 -> 置換後。順序が重要なので dict ではなくタプルで持つ。
_RULES = (
    (BACKSLASH, BACKSLASH + "textbackslash{}"),
    ("{", BACKSLASH + "{"),
    ("}", BACKSLASH + "}"),
    ("~", BACKSLASH + "textasciitilde{}"),
    ("^", BACKSLASH + "textasciicircum{}"),
    ("_", BACKSLASH + "_"),
    ("#", BACKSLASH + "#"),
    ("$", BACKSLASH + "$"),
    ("%", BACKSLASH + "%"),
    ("&", BACKSLASH + "&"),
)


def escape(text: str) -> str:
    """LaTeX の特殊文字を安全な形に置き換える."""
    out = []
    for ch in text:
        for src, dst in _RULES:
            if ch == src:
                out.append(dst)
                break
        else:
            out.append(ch)
    return "".join(out)


def tt(text: str) -> str:
    """等幅で安全に組む (graph6 文字列などに使う)."""
    return BACKSLASH + "texttt{" + escape(text) + "}"
