"""CLI: 探索 → 独立検証 → 日本語論文 (PDF) のパイプライン.

使い方::

    python -m mar list
    python -m mar survey  p0001_xxx
    python -m mar search  p0001_xxx --budget 120 --seed 0
    python -m mar verify  p0001_xxx          # 証明書 JSON だけを見る
    python -m mar paper   p0001_xxx
    python -m mar run     p0001_xxx          # search → verify → paper
    python -m mar verify --all               # 全証明書の再検査
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from .certificate import Certificate
from .problem import REPO_ROOT, iter_problem_modules, load
from .verification import load_record, render_record, save_record

CERT_DIR = REPO_ROOT / "data" / "certificates"

# Windows では標準出力が cp932 になり、日本語やダッシュで UnicodeEncodeError に
# なる (リダイレクト時に顕著)。検証結果が印字できずに落ちるのは致命的なので、
# 起動時に UTF-8 へ切り替える。
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):  # 差し替え済みのストリーム等
        pass


def cert_path(problem_id: str) -> Path:
    return CERT_DIR / f"{problem_id}.json"


def cmd_list(_: argparse.Namespace) -> int:
    for pid in iter_problem_modules():
        p = load(pid)
        status = "証明書あり" if cert_path(pid).exists() else "未探索"
        print(f"{pid:36s} {status:8s} {p.title}")
    return 0


def cmd_survey(args: argparse.Namespace) -> int:
    p = load(args.problem_id)
    s = p.survey
    print(f"# {p.title}\n")
    print(f"主張: {s.statement}\n")
    print(f"未解決と確認した日: {s.open_as_of}")
    if s.caveats:
        print("留意点:")
        for c in s.caveats:
            print(f"  - {c}")
    print("根拠:")
    for r in s.evidence:
        if isinstance(r, str):
            print(f"  - {r}")
        else:
            print(f"  - [{r.key}] {r.text} {r.url}".rstrip())
    if not s.evidence:
        print("  (なし) — 先行研究ゲート未通過。探索してはならない。")
        return 1
    return 0


def cmd_search(args: argparse.Namespace) -> int:
    p = load(args.problem_id)
    if not p.survey.evidence:
        print("先行研究ゲート未通過のため探索を中止する。", file=sys.stderr)
        return 1
    t0 = time.time()
    cert = p.search(budget_seconds=args.budget, seed=args.seed)
    dt = time.time() - t0
    if cert is None:
        print(f"探索は証明書を返さなかった ({dt:.1f} 秒)。")
        return 2
    path = cert.save(cert_path(p.problem_id))
    print(f"証明書を保存: {path} (digest={cert.digest()}, {dt:.1f} 秒)")
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    targets = iter_problem_modules() if args.all else [args.problem_id]
    failed = 0
    for pid in targets:
        path = cert_path(pid)
        if not path.exists():
            if args.all:
                continue
            print(f"証明書がない: {path}", file=sys.stderr)
            return 1
        cert = Certificate.load(path)
        if cert.problem_id != pid:
            print(f"[FAIL] {pid}: 証明書の problem_id 不一致", file=sys.stderr)
            failed += 1
            continue
        prob = load(pid)
        t0 = time.time()
        try:
            report = prob.verify(cert, deep=getattr(args, "deep", False))
        except TypeError:
            report = prob.verify(cert)
        dt = time.time() - t0
        print(f"# {pid}  digest={cert.digest()}")
        print(f"  主張: {cert.claim}")
        print(report.render())
        rec = save_record(cert, report, dt)
        print(f"  検証記録: {rec}")
        failed += 0 if report.ok else 1
    return 1 if failed else 0


def cmd_paper(args: argparse.Namespace) -> int:
    from .report.latex import make_paper
    p = load(args.problem_id)
    path = cert_path(p.problem_id)
    if not path.exists():
        print("証明書がない。先に search を実行する。", file=sys.stderr)
        return 1
    cert = Certificate.load(path)
    # 既定は「毎回検証をやり直す」(原則 4)。--use-record を明示したときだけ、
    # 同じ証明書・同じ検証器コードに対する PASS 記録で代替する。
    rec = load_record(cert) if getattr(args, "use_record", False) else None
    if rec is not None:
        print(f"検証をやり直さず記録を再利用 (--use-record, "
              f"digest={cert.digest()}):")
        print(render_record(rec))
    else:
        t0 = time.time()
        report = p.verify(cert)
        save_record(cert, report, time.time() - t0)
        if not report.ok:
            print("検証に失敗した証明書は論文化しない。\n" + report.render(),
                  file=sys.stderr)
            return 1
    pdf = make_paper(p, cert)
    print(f"PDF: {pdf}")
    return 0


def cmd_new(args: argparse.Namespace) -> int:
    from datetime import date

    from .scaffold import create
    try:
        made = create(args.problem_id, args.title, args.date or date.today().isoformat())
    except (ValueError, FileExistsError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    for path in made:
        print(f"作成: {path}")
    print("次: survey.evidence に未解決である根拠を書く "
          f"→ python -m mar survey {args.problem_id}")
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    for step in (cmd_search, cmd_verify, cmd_paper):
        rc = step(args)
        if rc != 0:
            return rc
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="mar", description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("list").set_defaults(func=cmd_list)

    sp = sub.add_parser("survey")
    sp.add_argument("problem_id")
    sp.set_defaults(func=cmd_survey)

    sp = sub.add_parser("paper")
    sp.add_argument("problem_id")
    sp.add_argument("--use-record", action="store_true", dest="use_record",
                    help="同じ証明書・同じ検証器コードの PASS 記録があれば "
                         "検証をやり直さない (既定はやり直す)")
    sp.set_defaults(func=cmd_paper)

    for name, func in (("search", cmd_search), ("run", cmd_run)):
        sp = sub.add_parser(name)
        sp.add_argument("problem_id")
        sp.add_argument("--budget", type=float, default=60.0)
        sp.add_argument("--seed", type=int, default=0)
        sp.add_argument("--deep", action="store_true")
        # run は verify → paper と続くので、直前の検証結果をそのまま使う。
        sp.set_defaults(func=func, all=False, use_record=True)

    sp = sub.add_parser("new", help="新しい問題モジュールの雛形を作る")
    sp.add_argument("problem_id", help="pNNNN_slug 形式")
    sp.add_argument("title", help="論文タイトル (日本語)")
    sp.add_argument("--date", help="未解決だと確認した日 (既定: 今日)")
    sp.set_defaults(func=cmd_new)

    sp = sub.add_parser("verify")
    sp.add_argument("problem_id", nargs="?")
    sp.add_argument("--all", action="store_true")
    sp.add_argument("--deep", action="store_true",
                    help="大きい族も含めて全数を独立実装で再計算する (遅い)")
    sp.set_defaults(func=cmd_verify)

    args = ap.parse_args(argv)
    if args.cmd == "verify" and not args.all and not args.problem_id:
        ap.error("verify には problem_id か --all が必要")
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
