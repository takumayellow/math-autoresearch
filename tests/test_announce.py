# -*- coding: utf-8 -*-
"""投稿文の組み立てに対する回帰テスト.

守りたい不変条件は 3 つ:

* 投稿文の**数値は手書きしない** (証明書の claim に現れる数字しか出ない)
* X の重み付き文字数で 280 を超えない
* LaTeX 片 (``$``, ``\\``) が投稿文に漏れない
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

import announce_backfill as backfill  # noqa: E402
from mar import announce  # noqa: E402
from mar.announce import state  # noqa: E402
from mar.announce.compose import (X_LIMIT, ComposeError, compose, detex,  # noqa: E402
                                  split_sentences, weighted_length)
from mar.announce.highlights import HIGHLIGHTS, highlight  # noqa: E402
from mar.problem import iter_problem_modules  # noqa: E402

URL = "https://github.com/takumayellow/math-autoresearch/blob/main/papers/x/main.pdf"


# --- 文字数 --------------------------------------------------------------

def test_weighted_length_counts_cjk_as_two():
    assert weighted_length("abc") == 3
    assert weighted_length("あいう") == 6
    assert weighted_length("a あ") == 4  # 1 + 1 + 2


def test_url_counts_as_23_regardless_of_length():
    short = "http://a.jp"
    long = "https://github.com/takumayellow/math-autoresearch/blob/main/x.pdf"
    assert weighted_length(short) == weighted_length(long) == 23


# --- LaTeX の除去 --------------------------------------------------------

@pytest.mark.parametrize("src,want", [
    (r"$\Delta \le 3$", "Δ ≤ 3"),
    (r"$\det JF \equiv -2$", "det JF ≡ -2"),
    (r"$\lceil \mathrm{diam}(G)/3 \rceil$", "⌈diam(G)/3⌉"),
    (r"$\frac{2}{3}$", "(2/3)"),
    (r"$F\colon \mathbb{C}^3 \to \mathbb{C}^3$", "F: C^3 → C^3"),
])
def test_detex(src, want):
    assert detex(src) == want


@pytest.mark.parametrize("src,want", [
    # 部分一致で置換すると意味が壊れる組。\to が \top を、\pm が \pmod を、
    # \le が \leftarrow を食ってはいけない。
    (r"$\top$", "⊤"),
    (r"$a \pmod n$", "a mod n"),
    (r"$A \rightarrow B$", "A → B"),
    (r"$\overline{G}$", "Ḡ"),
    (r"$\leftarrow$", "←"),
])
def test_detex_does_not_let_short_commands_eat_long_ones(src, want):
    assert detex(src) == want


def test_url_followed_by_japanese_is_not_swallowed():
    # \S+ だと URL の直後の日本語まで 23 文字ぶんとして数え、上限判定が甘くなる。
    assert weighted_length("http://a.jp。あ") == 23 + 2 + 2


def test_detex_keeps_unknown_command_names():
    # 消すと主張が変わる (\det が消えると「JF ≡ -2」になってしまう)。
    assert "det" in detex(r"$\det JF$")


def test_detex_joins_wrapped_japanese():
    assert detex("像点上の\nファイバー") == "像点上のファイバー"


def test_split_sentences_keeps_periods():
    assert split_sentences("あ。い。") == ["あ。", "い。"]


# --- 組み立て ------------------------------------------------------------

def test_compose_never_exceeds_limit_and_overflow_goes_to_replies():
    claim = "".join(f"文{i}は十分に長い日本語の文である。" * 2 for i in range(8))
    first, replies = compose("見出し", claim, URL, ("#数学",))
    assert weighted_length(first) <= X_LIMIT
    assert replies, "入りきらない分は返信に回る"
    for r in replies:
        assert weighted_length(r) <= X_LIMIT


def test_compose_does_not_cut_mid_sentence():
    claim = "短い文。" + "長い文" * 60 + "。"
    first, replies = compose("見出し", claim, URL)
    body = first.split("\n\n")[1]
    assert body == "短い文。"
    assert "".join(replies).startswith("長い文")


def test_compose_keeps_every_sentence_of_the_claim():
    """1 通目 + 返信を連結すると、主張の全文が復元できる (文を落とさない)."""
    claim = "".join(f"第{i}文はそれなりの長さをもつ日本語の文である。"
                    for i in range(6))
    first, replies = compose("見出し", claim, URL, ("#数学",))
    blocks = first.split("\n\n")
    body = blocks[1] if len(blocks) > 2 else ""
    assert body + "".join(replies) == "".join(split_sentences(detex(claim)))


def test_compose_refuses_to_drop_sentences_past_the_thread_limit():
    claim = "この文はそれなりに長い日本語の文である。" * 40
    with pytest.raises(ComposeError):
        compose("見出し", claim, URL, max_replies=1)


def test_compose_rejects_a_headline_that_cannot_fit():
    with pytest.raises(ComposeError):
        compose("あ" * 200, "主張。", URL)


def test_compose_puts_url_and_tags_in_the_first_post():
    first, _ = compose("見出し", "主張。", URL, ("#数学", "#グラフ理論"))
    assert URL in first and first.rstrip().endswith("#グラフ理論")


# --- 問題ごと ------------------------------------------------------------

def test_every_problem_has_a_headline():
    for pid in iter_problem_modules():
        assert highlight(pid).headline


def test_headlines_carry_no_numbers_except_conjecture_numbers():
    """見出しに走査数・反例数のような「成果の数値」を手書きしない.

    許すのは予想番号 (「予想 141」「予想 176 と 181」) と年 (「2026 年」)
    だけ。それ以外の裸の数字が出たら、証明書から引くべき数を手打ちしている。
    """
    allowed = re.compile(
        r"予想\s*[0-9]+(?:\s*[と・、,]\s*[0-9]+)*"
        r"|[0-9]+ 年")
    for pid, hl in HIGHLIGHTS.items():
        rest = allowed.sub("", hl.headline)
        assert not re.search(r"[0-9]", rest), (pid, hl.headline)


def test_ready_problems_are_postable_and_within_limit():
    ready = announce.ready_problems()
    assert ready, "検証済みの成果が 1 つもない"
    for pid in ready:
        post = announce.build_post(pid)
        assert post.weighted_length <= X_LIMIT
        for text in post.all_texts():
            assert "$" not in text and "\\" not in text
        assert post.pdf_url.endswith(f"papers/{pid}/main.pdf")
        assert announce.pdf_path(pid).exists()


def test_unverified_problem_is_not_postable(tmp_path, monkeypatch):
    monkeypatch.setattr(announce, "CERT_DIR", tmp_path)
    ok, why = announce.readiness("p0000_jacobian_2026")
    assert not ok and "証明書" in why


# --- 台帳 ----------------------------------------------------------------

def test_ledger_roundtrip_is_keyed_by_certificate_digest(tmp_path):
    path = tmp_path / "posted.json"
    rec = state.PostRecord("p0000", "aaaa", state.now_iso(), "本文",
                           tweet_id="1", tweet_url="u")
    state.append(rec, path)
    assert state.find("p0000", "aaaa", path) is not None
    # 証明書が変われば「未投稿」に戻る (= 更新版として投稿できる)
    assert state.find("p0000", "bbbb", path) is None


def test_dry_run_records_do_not_count_as_posted(tmp_path):
    path = tmp_path / "posted.json"
    state.append(state.PostRecord("p0000", "aaaa", state.now_iso(), "本文",
                                  dry_run=True), path)
    assert state.find("p0000", "aaaa", path) is None


def test_corrupt_ledger_fails_loudly_instead_of_looking_empty(tmp_path):
    """壊れた台帳を空と読み替えると、投稿済みの成果を全件再投稿してしまう."""
    path = tmp_path / "posted.json"
    path.write_text("{ これは JSON ではない", encoding="utf-8")
    with pytest.raises(state.LedgerError):
        state.load_ledger(path)
    with pytest.raises(state.LedgerError):
        state.find("p0000", "aaaa", path)


def test_ledger_record_missing_a_required_field_is_reported(tmp_path):
    path = tmp_path / "posted.json"
    path.write_text('{"posts": [{"problem_id": "p0000"}]}', encoding="utf-8")
    with pytest.raises(state.LedgerError):
        state.load_ledger(path)


# --- 台帳の書き戻し ------------------------------------------------------

def _post(problem_id: str, digest: str = "aaaa") -> announce.Post:
    return announce.Post(
        problem_id=problem_id, certificate_digest=digest, text="本文",
        replies=(), pdf_url=announce.pdf_url(problem_id), image=None,
        already_posted=None)


def _tweet(tweet_id: str, created_at: str, url: str) -> dict:
    return {"id": tweet_id, "created_at": created_at,
            "text": "本文 https://t.co/xxxx", "urls": [url]}


def test_backfill_matches_on_the_paper_url_not_on_the_text():
    """短縮 URL を展開して照合するので、問題を取り違えない."""
    target = _post("p0008_wowii141_girth_tree")
    other = _post("p0009_wowii2_leaf_local_indep")
    tweet = _tweet("1", "2026-09-01T00:00:00+00:00", target.pdf_url)
    assert backfill.matches(target, tweet)
    assert not backfill.matches(other, tweet)


def test_backfill_ignores_links_that_are_not_the_paper_pdf():
    """リポジトリ紹介やプレビュー画像のリンクを告知と取り違えない.

    取り違えると未投稿の成果が「投稿済み」になり、二度と告知されない。
    """
    post = _post("p0008_wowii141_girth_tree")
    preview = _tweet("1", "2026-09-01T00:00:00+00:00",
                     "https://github.com/takumayellow/math-autoresearch/"
                     "blob/main/papers/p0008_wowii141_girth_tree/preview/"
                     "page01.png")
    assert not backfill.matches(post, preview)


def test_backfill_does_not_treat_an_unknown_time_as_the_oldest():
    """時刻の取れないツイートを原投稿と誤認しない."""
    post = _post("p0008_wowii141_girth_tree")
    known = _tweet("1", "2026-09-01T00:00:00+00:00", post.pdf_url)
    unknown = _tweet("2", "", post.pdf_url)
    pairs = backfill.pair_up([post], [unknown, known])
    assert [t["id"] for _, t in pairs] == ["1"]


def test_backfill_fails_when_the_timeline_was_truncated(monkeypatch, capsys):
    """上限で打ち切ったまま「未投稿」と断定しない (= 再投稿しない)."""
    monkeypatch.setattr(backfill, "fetch_recent_tweets",
                        lambda limit: ([], False))
    assert backfill.main([]) == 1
    monkeypatch.setattr(backfill, "fetch_recent_tweets",
                        lambda limit: ([], True))
    assert backfill.main([]) == 0
    capsys.readouterr()


def test_backfill_picks_the_oldest_tweet_for_the_same_result():
    post = _post("p0008_wowii141_girth_tree")
    late = _tweet("2", "2026-09-05T00:00:00+00:00", post.pdf_url)
    early = _tweet("1", "2026-09-01T00:00:00+00:00", post.pdf_url)
    pairs = backfill.pair_up([post], [late, early])
    assert [(p.problem_id, t["id"]) for p, t in pairs] \
        == [(post.problem_id, "1")]


def test_backfill_record_keeps_the_tweet_id_and_original_time():
    post = _post("p0008_wowii141_girth_tree", digest="beef")
    rec = backfill.to_record(
        post, _tweet("42", "2026-09-01T00:00:00+00:00", post.pdf_url))
    assert rec.tweet_id == "42"
    assert rec.tweet_url.endswith("/42")
    assert rec.posted_at == "2026-09-01T00:00:00+00:00"
    assert rec.certificate_digest == "beef"
    assert not rec.dry_run  # 書き戻した記録は実投稿として数える
