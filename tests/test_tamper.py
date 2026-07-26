"""検証器が「嘘の証明書」を落とすことの回帰テスト.

「検証器は探索器から独立だ」という主張は、**正しい証明書が通ること**では
確かめられない。何も検査していない検証器でもそれは通る。確かめられるのは
**改竄した証明書が落ちること**だけである。ここでは証明書と証人を実際に
書き換えて、対応する検査項目が FAIL になることを確認する。

検証は元データ (McKay のリスト) の走査量に比例して重くなるので、テストでは
数秒で終わる小さい族だけに証明書を縮めてから走らせる。
"""

from __future__ import annotations

import copy
import gzip
import importlib
import shutil
import struct
from fractions import Fraction

import pytest

from mar.certificate import Certificate
from mar.problem import REPO_ROOT, load

CERT_DIR = REPO_ROOT / "data" / "certificates"
WITNESS_SRC = REPO_ROOT / "data" / "witnesses"

P0002 = "p0002_txgraffiti_zf_alpha"
P0003 = "p0003_saturation_harmonic"
P0004 = "p0004_wowii61_induced_forest"
P0005 = "p0005_wowii_induced_tree"
#: 元データの走査が軽く、かつ等号グラフを含む族。
P0002_FAMILIES = ("subcubic_06", "subcubic_08")
#: 反例は $n \ge 9$ にしか無いので、ここで検査するのは比と証人の側。
P0003_FAMILIES = ("graphs_06", "graphs_07")
#: 等号グラフを含み (n=6 で 11 個、n=7 で 32 個)、かつ数秒で走る族。
P0004_FAMILIES = ("graphs_06", "graphs_07")
#: 3 予想いずれの等号も現れ、かつ数秒で走る族。
P0005_FAMILIES = ("graphs_06", "graphs_07")


def _prepare(pid: str, keep, tmp_path, monkeypatch):
    """証明書を小さい族だけに縮め、証人を tmp にコピーして参照先を差し替える.

    返すのは (証明書, 問題インスタンス, 証人ディレクトリ)。証明書の ``data`` は
    複製なので、テスト側が自由に書き換えてよい。
    """
    path = CERT_DIR / f"{pid}.json"
    if not path.exists():
        pytest.skip(f"証明書がまだない: {path}")
    cert = Certificate.load(path)
    data = copy.deepcopy(cert.data)
    fams = [f for f in data["families"] if f["tag"] in keep]
    if len(fams) != len(keep):
        pytest.skip(f"{pid}: テストに必要な族が証明書にない")
    data["families"] = fams
    data["counterexamples"] = [c for c in data["counterexamples"]
                               if c.get("family", "") in keep or "family" not in c]
    wdir = tmp_path / "witnesses"
    wdir.mkdir()
    for fam in fams:
        shutil.copy2(WITNESS_SRC / fam["witness_file"], wdir / fam["witness_file"])
    monkeypatch.setattr(importlib.import_module(f"mar.problems.{pid}"),
                        "WITNESS_DIR", wdir)
    reduced = Certificate(problem_id=cert.problem_id, claim=cert.claim,
                          kind=cert.kind, data=data, provenance=cert.provenance)
    return reduced, load(pid), wdir


def _failed(report) -> str:
    """FAIL した検査項目のラベルを連結して返す (空文字なら全項目 PASS)."""
    return " | ".join(label for label, ok, _ in report.checks if not ok)


def _fam(cert: Certificate, tag: str) -> dict:
    return next(f for f in cert.data["families"] if f["tag"] == tag)


def _flip_first_byte(path):
    blob = bytearray(path.read_bytes())
    blob[0] ^= 0xFF
    path.write_bytes(bytes(blob))


# ----------------------------------------------------------------- p0002


@pytest.fixture()
def zf(tmp_path, monkeypatch):
    return _prepare(P0002, P0002_FAMILIES, tmp_path, monkeypatch)


def test_p0002_clean_certificate_verifies(zf):
    cert, prob, _ = zf
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0002_bit_flip_in_witness_is_detected(zf):
    cert, prob, wdir = zf
    _flip_first_byte(wdir / _fam(cert, "subcubic_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0002_forged_witness_with_updated_hash_is_detected(zf):
    """ハッシュも辻褄を合わせて証人を偽造しても、条件検査で落ちる."""
    import hashlib

    cert, prob, wdir = zf
    fam = _fam(cert, "subcubic_06")
    path = wdir / fam["witness_file"]
    blob = bytearray(path.read_bytes())
    # 先頭グラフの独立集合を空にする -> |S| <= |A|+1 = 1 が破れる
    struct.pack_into("<I", blob, 0, 0)
    path.write_bytes(bytes(blob))
    fam["witness_sha256"] = hashlib.sha256(bytes(blob)).hexdigest()
    report = prob.verify(cert)
    assert not report.ok
    assert "A が独立" in _failed(report)


def test_p0002_hidden_equality_graph_is_detected(zf):
    """等号グラフを 1 個隠すと、そのグラフで |S| <= |A| が破れて露見する."""
    cert, prob, _ = zf
    fam = _fam(cert, "subcubic_08")
    hidden = fam["equality_graphs"].pop()
    fam["counts"]["Z=alpha+1"] -= 1
    fam["counts"]["Z<=alpha"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert hidden in _failed(report) or "分類" in _failed(report)


def test_p0002_false_equality_claim_is_detected(zf):
    """等号でないグラフを等号リストに入れると、厳密再計算で露見する."""
    import mar.checkgraph as ck
    from mar.problems.p0002_txgraffiti_zf_alpha import _graph6_name

    cert, prob, _ = zf
    fam = _fam(cert, "subcubic_06")
    stats: dict = {}
    all_g6 = [ck.sets_to_graph6(g) for g in ck.read_bounded_degree(
        ck.GRAPH_DIR / _graph6_name(6), 3, stats)]
    innocent = next(g6 for g6 in all_g6 if g6 not in fam["equality_graphs"])
    fam["equality_graphs"].append(innocent)
    fam["counts"]["Z=alpha+1"] += 1
    fam["counts"]["Z<=alpha"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    assert "等号" in _failed(report)


def test_p0002_incomplete_equality_list_is_not_reported_as_closed(zf):
    """等号リストが完全でないなら「分類が閉じた」と報告してはならない."""
    cert, prob, _ = zf
    _fam(cert, "subcubic_06")["equality_complete"] = False
    report = prob.verify(cert)
    assert not report.ok
    assert "分類が閉じた" in _failed(report)


def test_p0002_wrong_published_count_is_detected(zf):
    """公表値は検証器が独自に持つので、証明書側の期待値を偽ると落ちる."""
    cert, prob, _ = zf
    _fam(cert, "subcubic_06")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0002_wrong_graph_count_is_detected(zf):
    cert, prob, _ = zf
    _fam(cert, "subcubic_08")["count"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "グラフ数" in _failed(report)


# ----------------------------------------------------------------- p0003


@pytest.fixture()
def sat(tmp_path, monkeypatch):
    return _prepare(P0003, P0003_FAMILIES, tmp_path, monkeypatch)


def test_p0003_clean_certificate_verifies(sat):
    cert, prob, _ = sat
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0003_bit_flip_in_witness_is_detected(sat):
    cert, prob, wdir = sat
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0003_non_maximal_matching_witness_is_detected(sat):
    """極大でないマッチングを証人にすると (ハッシュを直しても) 落ちる."""
    import hashlib

    cert, prob, wdir = sat
    fam = _fam(cert, "graphs_06")
    path = wdir / fam["witness_file"]
    blob = bytearray(gzip.decompress(path.read_bytes()))
    n = fam["n"]
    # 全バイト 0 の記録は「反例」の印なので、辺を 1 本外しても 0 にならない
    # (マッチングが 2 辺以上ある) グラフを選ぶ。
    base = next(i * n for i in range(fam["witness_records"])
                if sum(1 for b in blob[i * n:(i + 1) * n] if b) >= 4)
    v = next(j for j in range(n) if blob[base + j])
    partner = blob[base + v] - 1   # 頂点 v の相手
    blob[base + v] = 0             # 辺を 1 本外す -> 極大性が壊れる
    blob[base + partner] = 0
    raw = gzip.compress(bytes(blob))
    path.write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()
    assert len(blob) == n * fam["witness_records"]
    report = prob.verify(cert)
    assert not report.ok
    assert "極大マッチング" in _failed(report)


@pytest.mark.parametrize("scale", [Fraction(2), Fraction(1, 2)])
def test_p0003_wrong_max_ratio_is_detected(sat, scale):
    """最大比を過大にも過小にも偽れない (上下から挟んでいるため)."""
    cert, prob, _ = sat
    fam = _fam(cert, "graphs_07")
    fam["max_ratio"] = str(Fraction(fam["max_ratio"]) * scale)
    report = prob.verify(cert)
    assert not report.ok
    assert "最大比" in _failed(report)


def test_p0003_wrong_argmax_graph_is_detected(sat):
    """最大比の値が正しくても、達成グラフが違えば厳密再計算で落ちる."""
    import mar.checkgraph as ck
    from mar.problems.p0003_saturation_harmonic import _graph6_name

    cert, prob, _ = sat
    fam = _fam(cert, "graphs_06")
    claimed = Fraction(fam["max_ratio"])
    other = None
    for g in ck.read_graph6_file(ck.GRAPH_DIR / _graph6_name(6)):
        _, mu_star = ck.mu_and_mustar(g)
        if Fraction(mu_star) / ck.harmonic_index(g) != claimed:
            other = ck.sets_to_graph6(g)
            break
    assert other is not None, "比が全グラフで同じ族ではテストにならない"
    fam["max_ratio_g6"] = other
    report = prob.verify(cert)
    assert not report.ok
    assert "最大比" in _failed(report)


def test_p0003_missing_argmax_graph_is_detected(sat):
    cert, prob, _ = sat
    _fam(cert, "graphs_06")["max_ratio_g6"] = ""
    report = prob.verify(cert)
    assert not report.ok
    assert "最大比" in _failed(report)


def test_p0003_wrong_published_count_is_detected(sat):
    cert, prob, _ = sat
    _fam(cert, "graphs_07")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


# ----------------------------------------------------------------- p0004


@pytest.fixture()
def forest(tmp_path, monkeypatch):
    cert, prob, wdir = _prepare(P0004, P0004_FAMILIES, tmp_path, monkeypatch)
    # 族を間引いたので、合計も残った族に合わせ直す (検証器が突き合わせる)。
    fams = cert.data["families"]
    cert.data["totals"] = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "equality": sum(f["counts"].get("f=rhs", 0) for f in fams),
        "counterexamples": sum(f["counts"].get("f<rhs", 0) for f in fams),
        "exact_calls": sum(f["exact_calls"] for f in fams),
    }
    return cert, prob, wdir


def _p0004_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0004_wowii61_induced_forest import _verifier_source

    return list(_verifier_source(ck, fam))


def test_p0004_clean_certificate_verifies(forest):
    cert, prob, _ = forest
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0004_bit_flip_in_witness_is_detected(forest):
    cert, prob, wdir = forest
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0004_empty_witness_with_updated_hash_is_detected(forest):
    """空集合は森を誘導してしまうので、落ちるのは $|F| \\ge$ 右辺 の側."""
    import hashlib

    cert, prob, wdir = forest
    fam = _fam(cert, "graphs_06")
    path = wdir / fam["witness_file"]
    blob = bytearray(gzip.decompress(path.read_bytes()))
    struct.pack_into("<I", blob, 0, 0)      # 先頭グラフの証人を空集合にする
    raw = gzip.compress(bytes(blob))
    path.write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()
    report = prob.verify(cert)
    assert not report.ok
    assert "F が森を誘導し" in _failed(report)


def test_p0004_witness_with_a_cycle_is_detected(forest):
    """閉路を含む頂点集合を証人にすると森の判定で落ちる."""
    import hashlib

    import mar.checkgraph as ck

    cert, prob, wdir = forest
    fam = _fam(cert, "graphs_06")
    graphs = _p0004_graphs(fam)
    index = next(i for i, g in enumerate(graphs)
                 if not ck.induces_forest(g, set(range(fam["n"]))))
    path = wdir / fam["witness_file"]
    blob = bytearray(gzip.decompress(path.read_bytes()))
    # 全頂点を証人にする -> 閉路をもつグラフでは森でなくなる
    struct.pack_into("<I", blob, 4 * index, (1 << fam["n"]) - 1)
    raw = gzip.compress(bytes(blob))
    path.write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()
    report = prob.verify(cert)
    assert not report.ok
    assert "F が森を誘導し" in _failed(report)


def _detail(report, label_part: str) -> str:
    """指定した検査項目の detail を返す (どの防御が発火したかを見分けるため)."""
    return next(detail for label, ok, detail in report.checks
                if label_part in label and not ok)


def test_p0004_hidden_equality_graph_is_detected(forest):
    """等号グラフを 1 個隠すと、そのグラフで |F| >= 右辺 + 1 が破れる.

    個数の照合ではなく**証人の条件**が先に破れることまで確かめる (論文が
    謳っているのはそちらの機構なので、そこが死んでいたら気づけない)。
    """
    cert, prob, _ = forest
    fam = _fam(cert, "graphs_07")
    assert fam["equality_graphs"], "等号グラフを含む族でないとテストにならない"
    hidden = fam["equality_graphs"].pop()
    fam["counts"]["f=rhs"] -= 1
    fam["counts"]["f>rhs"] += 1
    cert.data["totals"]["equality"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類が閉じた")
    assert "等号リストに無いのに" in detail and hidden in detail


def test_p0004_false_equality_claim_is_detected(forest):
    """等号でないグラフを等号リストに入れると、厳密再計算で露見する."""
    import mar.checkgraph as ck

    cert, prob, _ = forest
    fam = _fam(cert, "graphs_06")
    listed = set(fam["equality_graphs"])
    innocent = next(g6 for g6 in (ck.sets_to_graph6(g) for g in _p0004_graphs(fam))
                    if g6 not in listed)
    fam["equality_graphs"].append(innocent)
    fam["counts"]["f=rhs"] += 1
    fam["counts"]["f>rhs"] -= 1
    cert.data["totals"]["equality"] += 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類が閉じた")
    assert "等号の主張が再現しない" in detail and innocent in detail


def test_p0004_incomplete_equality_list_is_not_reported_as_closed(forest):
    cert, prob, _ = forest
    _fam(cert, "graphs_06")["equality_complete"] = False
    report = prob.verify(cert)
    assert not report.ok
    assert "全リストが証明書にない" in _detail(report, "分類が閉じた")


def test_p0004_inflated_totals_are_detected(forest):
    """族ごとの集計と合わない合計 (論文の見出し数) は通さない."""
    cert, prob, _ = forest
    cert.data["totals"]["graphs"] += 1000
    report = prob.verify(cert)
    assert not report.ok
    assert "graphs" in _detail(report, "証明書の合計")


def test_p0004_wrong_published_count_is_detected(forest):
    cert, prob, _ = forest
    _fam(cert, "graphs_07")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0004_wrong_graph_count_is_detected(forest):
    cert, prob, _ = forest
    _fam(cert, "graphs_06")["count"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "グラフ数" in _failed(report)


# ----------------------------------------------------------------- p0005


P0005_CONJ = ("c142", "c144", "c146")


@pytest.fixture()
def tree3(tmp_path, monkeypatch):
    cert, prob, wdir = _prepare(P0005, P0005_FAMILIES, tmp_path, monkeypatch)
    fams = cert.data["families"]
    totals = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "equality": sum(f["counts"].get(f"{c}:equal", 0)
                        for f in fams for c in P0005_CONJ),
        "counterexamples": sum(f["counts"].get(f"{c}:fail", 0)
                               for f in fams for c in P0005_CONJ),
        "exact_calls": sum(f["exact_calls"] for f in fams),
    }
    for c in P0005_CONJ:
        totals[f"{c}:equal"] = sum(f["counts"].get(f"{c}:equal", 0) for f in fams)
        totals[f"{c}:fail"] = sum(f["counts"].get(f"{c}:fail", 0) for f in fams)
    cert.data["totals"] = totals
    return cert, prob, wdir


def _p0005_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0005_wowii_induced_tree import _verifier_source

    return list(_verifier_source(ck, fam))


def _rewrite_witness(wdir, fam: dict, index: int, mask: int) -> None:
    """証人 1 個を差し替え、SHA-256 も辻褄を合わせる (ハッシュ検査を素通しする)."""
    import hashlib

    path = wdir / fam["witness_file"]
    blob = bytearray(gzip.decompress(path.read_bytes()))
    struct.pack_into("<I", blob, 4 * index, mask)
    raw = gzip.compress(bytes(blob))
    path.write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()


def _lonely_equality(cert: Certificate):
    """ちょうど 1 本の予想でだけ等号になるグラフを (族, 予想, g6) で返す.

    2 本以上で等号のグラフを隠すと、残った側の再計算で先に落ちてしまい、
    「等号リストに無いのに狭義が閉じない」という本命の防御を試せない。
    """
    for fam in cert.data["families"]:
        lists = {c: set(fam.get("equality_graphs", {}).get(c, []))
                 for c in P0005_CONJ}
        for c in P0005_CONJ:
            others = set().union(*(lists[k] for k in P0005_CONJ if k != c))
            for g6 in sorted(lists[c] - others):
                return fam, c, g6
    return None, None, None


def test_p0005_clean_certificate_verifies(tree3):
    cert, prob, _ = tree3
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0005_bit_flip_in_witness_is_detected(tree3):
    cert, prob, wdir = tree3
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0005_empty_witness_is_detected(tree3):
    """空集合は木を誘導しない (p0004 の森と違い、ここは木の判定で落ちる)."""
    cert, prob, wdir = tree3
    fam = _fam(cert, "graphs_06")
    _rewrite_witness(wdir, fam, 0, 0)
    report = prob.verify(cert)
    assert not report.ok
    assert "T が木を誘導し" in _failed(report)


def test_p0005_witness_with_a_cycle_is_detected(tree3):
    """閉路を含む頂点集合を証人にすると木の判定で落ちる."""
    import mar.checkgraph as ck

    cert, prob, wdir = tree3
    fam = _fam(cert, "graphs_06")
    graphs = _p0005_graphs(fam)
    full = set(range(fam["n"]))
    index = next(i for i, g in enumerate(graphs) if not ck.induces_tree(g, full))
    _rewrite_witness(wdir, fam, index, (1 << fam["n"]) - 1)
    report = prob.verify(cert)
    assert not report.ok
    assert "T が木を誘導し" in _failed(report)


def test_p0005_too_small_witness_is_detected(tree3):
    """木ではあるが小さすぎる証人 (1 頂点) は下界に届かず落ちる.

    証人の**大きさ**を見ていない検証器はこれを通してしまう。上の 2 つ
    (木かどうか) とは別の防御なので、独立に試す。
    """
    import mar.checkgraph as ck

    cert, prob, wdir = tree3
    fam = _fam(cert, "graphs_06")
    graphs = _p0005_graphs(fam)
    index = next(i for i, g in enumerate(graphs)
                 if any(lhs > rhs
                        for lhs, rhs in ck.induced_tree_bounds(g, 1).values()))
    _rewrite_witness(wdir, fam, index, 1)   # 頂点 0 だけ = 1 頂点の木
    report = prob.verify(cert)
    assert not report.ok
    assert "下界に届かない" in _detail(report, "T が木を誘導し")


def test_p0005_out_of_range_witness_is_detected(tree3):
    """存在しない頂点を含むマスクを弾く."""
    cert, prob, wdir = tree3
    fam = _fam(cert, "graphs_06")
    _rewrite_witness(wdir, fam, 0, 1 << (fam["n"] + 1))
    report = prob.verify(cert)
    assert not report.ok
    assert "T が木を誘導し" in _failed(report)


def test_p0005_hidden_equality_graph_is_detected(tree3):
    """等号グラフを 1 個隠すと、そのグラフで狭義の不等式が破れる."""
    cert, prob, _ = tree3
    fam, conj, hidden = _lonely_equality(cert)
    assert hidden, "1 本だけで等号になるグラフが族に無いとテストにならない"
    fam["equality_graphs"][conj].remove(hidden)
    fam["counts"][f"{conj}:equal"] -= 1
    fam["counts"][f"{conj}:strict"] += 1
    cert.data["totals"]["equality"] -= 1
    cert.data["totals"][f"{conj}:equal"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類が閉じた")
    assert "等号リストに" in detail and hidden in detail


def test_p0005_false_equality_claim_is_detected(tree3):
    """等号でないグラフを等号リストに入れると、厳密再計算で露見する."""
    import mar.checkgraph as ck

    cert, prob, _ = tree3
    fam = _fam(cert, "graphs_06")
    listed = set().union(*(set(fam["equality_graphs"].get(c, []))
                           for c in P0005_CONJ))
    innocent = next(g6 for g6 in (ck.sets_to_graph6(g) for g in _p0005_graphs(fam))
                    if g6 not in listed)
    fam["equality_graphs"]["c142"].append(innocent)
    fam["counts"]["c142:equal"] += 1
    fam["counts"]["c142:strict"] -= 1
    cert.data["totals"]["equality"] += 1
    cert.data["totals"]["c142:equal"] += 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類が閉じた")
    assert "等号の主張が再現しない" in detail and innocent in detail


def test_p0005_equality_moved_to_another_conjecture_is_detected(tree3):
    """どの予想で等号かを取り違えた証明書も落ちる (3 本まとめて扱う分の防御)."""
    cert, prob, _ = tree3
    fam, conj, g6 = _lonely_equality(cert)
    assert g6, "1 本だけで等号になるグラフが族に無いとテストにならない"
    other = next(c for c in P0005_CONJ if c != conj)
    fam["equality_graphs"][conj].remove(g6)
    fam["equality_graphs"].setdefault(other, []).append(g6)
    fam["counts"][f"{conj}:equal"] -= 1
    fam["counts"][f"{conj}:strict"] += 1
    fam["counts"][f"{other}:equal"] += 1
    fam["counts"][f"{other}:strict"] -= 1
    cert.data["totals"][f"{conj}:equal"] -= 1
    cert.data["totals"][f"{other}:equal"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "等号の主張が再現しない" in _detail(report, "分類が閉じた")


def test_p0005_incomplete_equality_list_is_not_reported_as_closed(tree3):
    cert, prob, _ = tree3
    _fam(cert, "graphs_06")["equality_complete"] = False
    report = prob.verify(cert)
    assert not report.ok
    assert "全リストが証明書にない" in _detail(report, "分類が閉じた")


def test_p0005_inflated_totals_are_detected(tree3):
    cert, prob, _ = tree3
    cert.data["totals"]["c146:equal"] += 7
    report = prob.verify(cert)
    assert not report.ok
    assert "c146:equal" in _detail(report, "証明書の合計")


def test_p0005_wrong_published_count_is_detected(tree3):
    cert, prob, _ = tree3
    _fam(cert, "graphs_07")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0005_wrong_graph_count_is_detected(tree3):
    cert, prob, _ = tree3
    _fam(cert, "graphs_06")["count"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "グラフ数" in _failed(report)


def test_p0005_truncated_witness_file_is_detected(tree3):
    """証人を後ろから削ると、例外ではなく不合格として報告される."""
    import hashlib

    cert, prob, wdir = tree3
    fam = _fam(cert, "graphs_06")
    path = wdir / fam["witness_file"]
    raw = gzip.compress(gzip.decompress(path.read_bytes())[:-4])
    path.write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()
    fam["witness_records"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    assert "証人の個数が元リストより少ない" in _detail(report, "T が木を誘導")


def test_p0005_bogus_equality_example_is_detected(tree3):
    """論文に載る等号グラフの例が等号リスト外なら不合格になる."""
    cert, prob, _ = tree3
    fam = _fam(cert, "graphs_06")
    fam["equality_examples"]["c142"] = ["E????"] + \
        fam["equality_examples"].get("c142", [])
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類が閉じた")
    assert "等号リストに無いグラフが例に載っている" in detail
