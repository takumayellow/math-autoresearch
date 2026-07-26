"""実行環境の OS 名を正しく取る.

``platform.release()`` は Windows 11 でも ``"10"`` を返す (Python は
``GetVersionEx`` 系の互換値を見るため)。証明書の再現性メタデータは論文の
「実行環境」欄にそのまま印字されるので、ここが嘘だと本稿の主張全体の
検証可能性が疑われる。ビルド番号 22000 以上なら Windows 11 と判定して
実際のビルドまで書く。
"""

from __future__ import annotations

import platform
import sys

#: Windows 11 の最初のビルド番号 (Microsoft の公表値)。
WIN11_FIRST_BUILD = 22000


def os_label() -> str:
    """``"Windows 11 (build 26200)"`` のような表示名を返す."""
    system = platform.system()
    if system != "Windows":
        return f"{system} {platform.release()}".strip()
    try:
        build = sys.getwindowsversion().build
    except (AttributeError, OSError):
        return f"Windows {platform.release()}"
    major = 11 if build >= WIN11_FIRST_BUILD else 10
    return f"Windows {major} (build {build})"
