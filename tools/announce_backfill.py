"""既に X に投稿済みの成果を、タイムラインから照合して台帳に書き戻す.

``mar announce --post`` は ``data/announce/posted.json`` (投稿台帳) に無い
ものを未投稿とみなす。台帳ができる前に手で投稿した分が残っていると、
``--all`` で**同じ成果をもう一度投稿してしまう**。

そこで、資格情報が使えるようになった時点でこのツールを 1 回走らせ、
自分のタイムラインと突き合わせて台帳を作る。照合の鍵は投稿文に入る
論文 PDF の URL (``papers/<問題 id>/main.pdf``) で、これは問題ごとに
一意なので取り違えない。URL は t.co に短縮されるため、API v2 の
``entities.urls[].expanded_url`` を見る。

既定は**読むだけ**。``--write`` を付けたときだけ台帳に追記する::

    PYTHONPATH=src python tools/announce_backfill.py          # 照合結果を見る
    PYTHONPATH=src python tools/announce_backfill.py --write  # 台帳に書く

タイムラインは新しい順にしか読めないので、``--limit`` まで遡って
**見つからなかった成果が残った**ときは、その成果が本当に未投稿なのか
上限の外にあるだけなのか区別できない。この場合は終了コード 1 を返す
(``--limit`` を伸ばして引き直す)。ここで「未投稿」と決めつけるのが
再投稿そのものなので、黙って 0 を返さない。

記録する ``certificate_digest`` は**今の**証明書のもの。投稿してから
証明書を作り直していると、古い版を告知したツイートに新しい digest を
刻むことになり、更新版の告知が出なくなる。証明書の ``created_at`` が
ツイートより新しい対は警告を出すので、内容を更新していたならその記録を
台帳から消して告知し直す。
"""

from __future__ import annotations

import argparse
import sys
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))

from mar import announce  # noqa: E402
from mar.announce import state, xclient  # noqa: E402

#: 1 回の照合で遡るツイート数の上限。
DEFAULT_LIMIT = 200


class BackfillError(RuntimeError):
    """タイムラインが読めない."""


def fetch_recent_tweets(limit: int = DEFAULT_LIMIT) -> tuple[list[dict], bool]:
    """自分の直近ツイートと、**最後まで読み切ったか**を返す.

    ツイートは ``{"id", "created_at", "text", "urls"}``。第 2 要素が False の
    ときは ``limit`` で打ち切っており、それより古い投稿は見えていない。
    """
    try:
        import tweepy  # 遅延 import: 照合しないときは不要
    except ImportError as exc:  # pragma: no cover - 環境依存
        raise BackfillError(
            "tweepy が入っていない。`pip install tweepy` を実行する。") from exc

    creds = xclient.load_credentials()
    client = tweepy.Client(
        consumer_key=creds.api_key, consumer_secret=creds.api_secret,
        access_token=creds.access_token,
        access_token_secret=creds.access_token_secret)
    try:
        me = client.get_me()
        if me.data is None:
            raise BackfillError("get_me が空を返した (資格情報を確認する)")
        pages = tweepy.Paginator(
            client.get_users_tweets, me.data.id,
            max_results=100, exclude=["retweets"],
            tweet_fields=["created_at", "entities"], limit=(limit // 100) + 1)
        out = []
        for page in pages:
            for tw in page.data or []:
                urls = [u.get("expanded_url", "")
                        for u in (tw.entities or {}).get("urls", [])]
                out.append({
                    "id": str(tw.id),
                    "created_at": (tw.created_at.isoformat()
                                   if tw.created_at else ""),
                    "text": tw.text or "",
                    "urls": urls,
                })
                if len(out) >= limit:
                    return out, False
        return out, True
    except Exception as exc:  # pragma: no cover - ネットワーク依存
        if isinstance(exc, BackfillError):
            raise
        raise BackfillError(f"タイムラインが読めない: {exc}") from exc


def matches(post: announce.Post, tweet: dict) -> bool:
    """この成果の告知かどうか (論文 PDF の URL が一致するかで判定).

    ``papers/<id>/`` の部分一致ではなく ``main.pdf`` まで含む完全な URL を
    見る。プレビュー画像やリポジトリ紹介のリンクを告知と取り違えると、
    未投稿の成果が「投稿済み」になって二度と告知されない。
    """
    needle = post.pdf_url
    if any(url.startswith(needle) for url in tweet["urls"]):
        return True
    return needle in tweet["text"]


def _age_key(tweet: dict) -> tuple[bool, str]:
    """古い順に並べる鍵。時刻不明は最後に回す.

    空文字を素朴に比較すると「いちばん古い」と読まれ、原投稿ではなく
    時刻の取れなかった返信を記録してしまう。
    """
    return (tweet["created_at"] == "", tweet["created_at"])


def pair_up(posts: list[announce.Post],
            tweets: list[dict]) -> list[tuple[announce.Post, dict]]:
    """成果とツイートの対応。同じ成果が複数あれば最も古いものを採る."""
    pairs = []
    for post in posts:
        hits = [tw for tw in tweets if matches(post, tw)]
        if hits:
            pairs.append((post, min(hits, key=_age_key)))
    return pairs


def certificate_is_newer(post: announce.Post, tweet: dict) -> bool:
    """証明書がツイートより後に作られているか.

    後なら、そのツイートは**別の版**を告知した可能性がある。今の digest を
    「投稿済み」として刻むと更新版の告知が出なくなるので、警告を出す。
    """
    from mar.certificate import Certificate

    created = Certificate.load(
        announce.CERT_DIR / f"{post.problem_id}.json").provenance.created_at
    if not created or not tweet["created_at"]:
        return False
    try:  # 文字列比較だとタイムゾーン表記の差で狂う
        return (datetime.fromisoformat(created)
                > datetime.fromisoformat(tweet["created_at"]))
    except ValueError:
        return False


def to_record(post: announce.Post, tweet: dict) -> state.PostRecord:
    return state.PostRecord(
        problem_id=post.problem_id,
        certificate_digest=post.certificate_digest,
        posted_at=tweet["created_at"] or state.now_iso(),
        text=tweet["text"],
        tweet_id=tweet["id"],
        tweet_url=f"https://x.com/i/web/status/{tweet['id']}",
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                        help=f"遡るツイート数 (既定 {DEFAULT_LIMIT})")
    parser.add_argument("--write", action="store_true",
                        help="照合できた分を台帳に追記する")
    args = parser.parse_args(argv)

    try:
        tweets, exhausted = fetch_recent_tweets(args.limit)
    except (BackfillError, xclient.CredentialsError) as exc:
        print(exc, file=sys.stderr)
        return 1
    print(f"タイムライン {len(tweets)} 件を取得"
          f"{'' if exhausted else f' (上限 {args.limit} で打ち切り)'}")

    posts = [announce.build_post(pid) for pid in announce.ready_problems()]
    pairs = pair_up(posts, tweets)

    for post, tweet in pairs:
        known = post.already_posted is not None
        print(f"  {post.problem_id}  digest={post.certificate_digest}"
              f"  tweet={tweet['id']}  {tweet['created_at']}"
              f"  {'[台帳にある]' if known else '[台帳に無い]'}")
        if certificate_is_newer(post, tweet):
            print(f"    警告: 証明書がこのツイートより後に作られている。"
                  f"内容を更新していたなら、{post.problem_id} の記録を台帳から"
                  f"消して告知し直す")

    fresh = [(p, t) for p, t in pairs if p.already_posted is None]
    if args.write and fresh:
        for post, tweet in fresh:
            path = state.append(to_record(post, tweet))
            print(f"台帳に追記: {post.problem_id} -> {path}")
    elif fresh:
        print(f"\n{len(fresh)} 件が台帳に無い。"
              "書き戻すなら --write を付けて実行する")
    elif pairs:
        print("すべて台帳にある。追記することは無い")
    else:
        print("投稿済みの成果は見つからなかった")

    # 見つからなかった成果が残っていて、かつタイムラインを読み切っていない
    # なら、「未投稿」と断定できない。ここで 0 を返すと再投稿につながる。
    missing = [p.problem_id for p in posts
               if not any(q.problem_id == p.problem_id for q, _ in pairs)]
    if missing and not exhausted:
        print(f"\n照合できなかった成果が {len(missing)} 件ある一方で、"
              f"タイムラインは上限 {args.limit} 件で打ち切っている。"
              f"未投稿とは断定できないので --limit を伸ばして引き直す:\n"
              f"  {', '.join(missing)}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
