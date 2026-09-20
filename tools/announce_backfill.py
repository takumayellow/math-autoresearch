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

記録する ``certificate_digest`` は**今の**証明書のもの。投稿後に探索を
やり直して証明書が変わっていれば digest が合わず「更新版」として再投稿
対象に戻るが、それは台帳の設計どおりの挙動である。
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))

from mar import announce  # noqa: E402
from mar.announce import state, xclient  # noqa: E402

#: 1 回の照合で遡るツイート数の上限。
DEFAULT_LIMIT = 200


class BackfillError(RuntimeError):
    """タイムラインが読めない."""


def fetch_recent_tweets(limit: int = DEFAULT_LIMIT) -> list[dict]:
    """自分の直近ツイートを ``{"id", "created_at", "text", "urls"}`` で返す."""
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
                    return out
        return out
    except Exception as exc:  # pragma: no cover - ネットワーク依存
        if isinstance(exc, BackfillError):
            raise
        raise BackfillError(f"タイムラインが読めない: {exc}") from exc


def matches(post: announce.Post, tweet: dict) -> bool:
    """この成果の投稿かどうか (PDF の URL が一致するかで判定)."""
    needle = f"papers/{post.problem_id}/"
    if any(needle in url for url in tweet["urls"]):
        return True
    return needle in tweet["text"]


def pair_up(posts: list[announce.Post],
            tweets: list[dict]) -> list[tuple[announce.Post, dict]]:
    """成果とツイートの対応。同じ成果が複数あれば最も古いものを採る."""
    pairs = []
    for post in posts:
        hits = [tw for tw in tweets if matches(post, tw)]
        if hits:
            pairs.append((post, min(hits, key=lambda tw: tw["created_at"])))
    return pairs


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
        tweets = fetch_recent_tweets(args.limit)
    except (BackfillError, xclient.CredentialsError) as exc:
        print(exc, file=sys.stderr)
        return 1
    print(f"タイムライン {len(tweets)} 件を取得")

    posts = [announce.build_post(pid) for pid in announce.ready_problems()]
    pairs = pair_up(posts, tweets)
    if not pairs:
        print("投稿済みの成果は見つからなかった (台帳は空のままでよい)")
        return 0

    for post, tweet in pairs:
        known = post.already_posted is not None
        print(f"  {post.problem_id}  digest={post.certificate_digest}"
              f"  tweet={tweet['id']}  {tweet['created_at']}"
              f"  {'[台帳にある]' if known else '[台帳に無い]'}")

    fresh = [(p, t) for p, t in pairs if p.already_posted is None]
    if not fresh:
        print("すべて台帳にある。追記することは無い")
        return 0
    if not args.write:
        print(f"\n{len(fresh)} 件が台帳に無い。"
              "書き戻すなら --write を付けて実行する")
        return 0
    for post, tweet in fresh:
        path = state.append(to_record(post, tweet))
        print(f"台帳に追記: {post.problem_id} -> {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
