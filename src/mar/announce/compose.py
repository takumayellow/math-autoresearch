"""投稿文の組み立てと X の文字数計算.

方針は本文 (論文) と同じで、**数値を手で書かない**。投稿文に現れる数
(走査したグラフの個数、等号の個数、反例の個数) は、すべて証明書の
``claim`` から**そのまま**持ってくる。手で書いてよいのは数を含まない
見出しだけ (:mod:`mar.announce.highlights`)。claim が長い場合は
**文単位で先頭から採る**。文の途中で切ると主張が変質するので切らない。
"""

from __future__ import annotations

import re
import unicodedata

#: X の重み。CJK は 2 カウントなので、日本語は実質 140 文字。
X_LIMIT = 280
#: t.co に短縮された後の URL の重み (X の設定値)。
URL_WEIGHT = 23

#: URL に使える文字だけを食う (``\S+`` だと直後の日本語まで飲み込み、
#: 23 文字ぶんとして数えてしまって上限判定が甘くなる)。
_URL_RE = re.compile(r"https?://[A-Za-z0-9\-._~:/?#\[\]@!$&'()*+,;=%]+")

#: 重み 1 の符号位置 (X の weightedLength 仕様)。それ以外は 2。
_LIGHT_RANGES = ((0x0000, 0x10FF), (0x2000, 0x200D),
                 (0x2010, 0x201F), (0x2032, 0x2037))


def _char_weight(ch: str) -> int:
    cp = ord(ch)
    return 1 if any(lo <= cp <= hi for lo, hi in _LIGHT_RANGES) else 2


def weighted_length(text: str) -> int:
    """X の重み付き文字数。URL は短縮後の固定長で数える.

    X は数える前に NFC 正規化するので、こちらも合わせる (合成前の
    「か + 濁点」を 2 文字と数えると、実際より長く見積もってしまう)。
    """
    text = unicodedata.normalize("NFC", text)
    total = 0
    pos = 0
    for m in _URL_RE.finditer(text):
        total += sum(_char_weight(c) for c in text[pos:m.start()])
        total += URL_WEIGHT
        pos = m.end()
    total += sum(_char_weight(c) for c in text[pos:])
    return total


# ---------------------------------------------------------------------------
# LaTeX 片を平文に落とす
# ---------------------------------------------------------------------------

_SYMBOLS = {
    r"\le": "≤", r"\leq": "≤", r"\ge": "≥", r"\geq": "≥", r"\neq": "≠",
    r"\times": "×", r"\cdot": "・", r"\pm": "±", r"\equiv": "≡",
    r"\to": "→", r"\rightarrow": "→", r"\leftarrow": "←",
    r"\Rightarrow": "⇒", r"\Leftrightarrow": "⇔", r"\mapsto": "↦",
    r"\pmod": "mod", r"\bmod": "mod", r"\top": "⊤", r"\bot": "⊥",
    r"\colon": ":", r"\ldots": "…", r"\dots": "…", r"\cdots": "…",
    r"\alpha": "α", r"\beta": "β", r"\gamma": "γ", r"\delta": "δ",
    r"\Delta": "Δ", r"\ell": "l", r"\mu": "μ", r"\sigma": "σ",
    r"\kappa": "κ", r"\lambda": "λ", r"\rho": "ρ", r"\tau": "τ",
    r"\varepsilon": "ε", r"\epsilon": "ε", r"\omega": "ω", r"\Omega": "Ω",
    r"\phi": "φ", r"\varphi": "φ", r"\theta": "θ", r"\pi": "π",
    r"\in": "∈", r"\notin": "∉", r"\subseteq": "⊆", r"\subset": "⊂",
    r"\cup": "∪", r"\cap": "∩", r"\setminus": "＼", r"\emptyset": "∅",
    r"\infty": "∞", r"\sim": "〜", r"\simeq": "≃", r"\cong": "≅",
    r"\approx": "≈", r"\mid": "|", r"\sum": "Σ", r"\prod": "Π",
    r"\left": "", r"\right": "", r"\,": " ", r"\;": " ",
    r"\ ": " ", r"\!": "",
}

#: ``\le`` が ``\leq`` を、``\to`` が ``\top`` を食い合わないよう、長い名前
#: から順に、英字コマンドは直後に英字が来ないときだけ置換する。
_SYMBOL_RE = re.compile("|".join(
    re.escape(name) + (r"(?![A-Za-z])" if name[-1].isalpha() else "")
    for name in sorted(_SYMBOLS, key=len, reverse=True)))

#: 上線 (補グラフ・共役)。中身を消すと主張が変わるので結合マクロンを付ける。
_OVERLINE = re.compile(r"\\overline\s*\{([^{}]*)\}")

_CMD_ARG = re.compile(r"\\(?:mathrm|mathbb|mathcal|text|texttt|emph|operatorname)"
                      r"\{([^{}]*)\}")
_FRAC = re.compile(r"\\frac\{([^{}]*)\}\{([^{}]*)\}")
_CEIL = re.compile(r"\\lceil(.*?)\\rceil")
_FLOOR = re.compile(r"\\lfloor(.*?)\\rfloor")
_LEFTOVER_CMD = re.compile(r"\\[A-Za-z]+")
#: 仮名・漢字・全角句読点 (この間の空白だけを詰める)
_CJK = r"々぀-ヿ㐀-䶿一-鿿、。（）"


def detex(text: str) -> str:
    """証明書の claim に混ざる LaTeX 片を、読める平文に落とす.

    投稿文にバックスラッシュや ``$`` を残さないことがこの関数の責務。
    """
    out = text.replace("$$", "$")
    out = _OVERLINE.sub(lambda m: m.group(1).strip() + "̄", out)
    out = _FRAC.sub(r"(\1/\2)", out)
    out = _CEIL.sub(lambda m: "⌈" + m.group(1).strip() + "⌉", out)
    out = _FLOOR.sub(lambda m: "⌊" + m.group(1).strip() + "⌋", out)
    for _ in range(3):  # \mathrm{\ldots} のような入れ子を数回で潰す
        new = _CMD_ARG.sub(r"\1", out)
        if new == out:
            break
        out = new
    out = _SYMBOL_RE.sub(lambda m: _SYMBOLS[m.group(0)], out)
    # 未知のコマンドは消さずに名前を残す (\det を消すと主張が変わる)。
    out = _LEFTOVER_CMD.sub(lambda m: m.group(0)[1:], out)
    out = out.replace("$", "").replace("{", "").replace("}", "")
    out = out.replace("\\", "")
    # 原文の改行や字下げ。仮名・漢字どうしの間なら詰め、そうでなければ空白 1 個
    # (記号の間で詰めると "Δ ≤ 3" が "Δ≤ 3" になって読みにくい)。
    out = re.sub(r"\s+", " ", out)
    out = re.sub(rf"(?<=[{_CJK}])\s+(?=[{_CJK}])", "", out)
    return out.strip()


def split_sentences(text: str) -> list[str]:
    """日本語の句点で文に割る (句点は残す)."""
    parts = re.findall(r"[^。]*。|[^。]+$", text)
    return [p for p in (s.strip() for s in parts) if p]


# ---------------------------------------------------------------------------
# 組み立て
# ---------------------------------------------------------------------------

class ComposeError(ValueError):
    """投稿文が組めない (見出しが長すぎる / スレッドに収まらない).

    黙って文を捨てると主張が変質するので、収まらないときは必ず失敗させる。
    """


def _split_by_weight(text: str, limit: int) -> list[str]:
    """1 文が上限を超える場合だけ、重み基準で機械的に割る."""
    chunks, buf, width = [], [], 0
    for ch in text:
        w = _char_weight(ch)
        if width + w > limit and buf:
            chunks.append("".join(buf))
            buf, width = [], 0
        buf.append(ch)
        width += w
    if buf:
        chunks.append("".join(buf))
    return chunks


def _pack(sentences: list[str], limit: int) -> list[str]:
    """文を順に、上限を超えない塊にまとめる (文の途中では切らない)."""
    out: list[str] = []
    buf = ""
    for sent in sentences:
        if weighted_length(sent) > limit:
            if buf:
                out.append(buf)
                buf = ""
            out.extend(_split_by_weight(sent, limit))
            continue
        if buf and weighted_length(buf + sent) > limit:
            out.append(buf)
            buf = sent
        else:
            buf += sent
    if buf:
        out.append(buf)
    return out


def compose(headline: str, claim: str, url: str, tags: tuple[str, ...] = (),
            limit: int = X_LIMIT,
            max_replies: int = 3) -> tuple[str, list[str]]:
    """見出し + 証明書の主張 + PDF リンク + タグ を組み、スレッドにして返す.

    1 通目に入りきらなかった主張の続きは、返信 (スレッド) に回す。**文の
    途中では切らない** (1 文が上限を超えるときだけ機械的に割る)。戻り値は
    ``(1 通目, 続きのリスト)``。
    """
    body_all = split_sentences(detex(claim))
    tail = [url] + ([" ".join(tags)] if tags else [])

    def render(body: list[str]) -> str:
        blocks = [headline.strip()]
        if body:
            blocks.append("".join(body))
        return "\n\n".join(blocks + ["\n".join(tail)])

    for k in range(len(body_all), -1, -1):
        text = render(body_all[:k])
        if weighted_length(text) <= limit:
            replies = _pack(body_all[k:], limit)
            if len(replies) > max_replies:
                raise ComposeError(
                    f"主張がスレッド {max_replies} 通に収まらない "
                    f"({len(replies)} 通必要)。claim を短くするか "
                    f"max_replies を上げる。")
            return text, replies
    raise ComposeError(
        f"見出しだけで上限を超える ({weighted_length(render([]))} > {limit}): "
        f"{headline!r}")
