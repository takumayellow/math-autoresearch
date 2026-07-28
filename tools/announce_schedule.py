# -*- coding: utf-8 -*-
"""1 日 1 件だけ成果を X に投稿する Windows タスクを登録する.

X API の予約投稿は使わない (有料プランの機能)。代わりに「毎日 1 件、未投稿
の成果があれば投稿する」タスクを OS 側に置く。投稿対象がなければ何もせず
終わるので、成果が溜まった順に自然に流れていく。

使い方::

    python tools/announce_schedule.py            # 登録 (既定 19:00)
    python tools/announce_schedule.py --at 21:30
    python tools/announce_schedule.py --status
    python tools/announce_schedule.py --remove

登録されるコマンドは ``python -m mar announce --next --post`` で、投稿の
可否は :mod:`mar.announce` の判定 (検証済み・PDF あり・未投稿) に従う。
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

TASK_NAME = "MathAutoresearch_X_DailyPost"
REPO = Path(__file__).resolve().parents[1]
LOG = REPO / "data" / "announce" / "schedule.log"


def _task_command() -> str:
    """cmd.exe 一行。src を PYTHONPATH に入れ、出力をログに追記する."""
    # パスに空白や cmd のメタ文字が入っても壊れないよう、すべて引用符で囲む。
    return (
        f'cmd /c "cd /d "{REPO}" '
        f'&& set "PYTHONPATH={REPO / "src"}" '
        f'&& set PYTHONIOENCODING=utf-8 '
        f'&& "{sys.executable}" -m mar announce --next --post '
        f'>> "{LOG}" 2>&1"'
    )


def _run(cmd: list[str]) -> tuple[int, str]:
    r = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def register(at: str) -> int:
    LOG.parent.mkdir(parents=True, exist_ok=True)
    code, out = _run(["schtasks", "/Create", "/TN", TASK_NAME,
                      "/TR", _task_command(), "/SC", "DAILY", "/ST", at, "/F"])
    print(out.strip())
    if code != 0:
        return code
    print(f"登録した: {TASK_NAME} (毎日 {at})")
    print(f"ログ: {LOG}")
    print(f"手動実行: schtasks /Run /TN {TASK_NAME}")
    return 0


def remove() -> int:
    code, out = _run(["schtasks", "/Delete", "/TN", TASK_NAME, "/F"])
    print(out.strip())
    return code


def status() -> int:
    code, out = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(out.strip() or "(未登録)")
    return code


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--at", default="19:00", help="毎日の実行時刻 (既定 19:00)")
    ap.add_argument("--remove", action="store_true")
    ap.add_argument("--status", action="store_true")
    args = ap.parse_args(argv)
    if args.remove:
        return remove()
    if args.status:
        return status()
    return register(args.at)


if __name__ == "__main__":
    raise SystemExit(main())
