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
P0006 = "p0006_wowii194_hamiltonian"
P0007 = "p0007_wowii200_star_tree"
P0008 = "p0008_wowii141_girth_tree"
P0009 = "p0009_wowii2_leaf_local_indep"
#: 元データの走査が軽く、かつ等号グラフを含む族。
P0002_FAMILIES = ("subcubic_06", "subcubic_08")
#: 反例は $n \ge 9$ にしか無いので、ここで検査するのは比と証人の側。
P0003_FAMILIES = ("graphs_06", "graphs_07")
#: 等号グラフを含み (n=6 で 11 個、n=7 で 32 個)、かつ数秒で走る族。
P0004_FAMILIES = ("graphs_06", "graphs_07")
#: 3 予想いずれの等号も現れ、かつ数秒で走る族。
P0005_FAMILIES = ("graphs_06", "graphs_07")
#: 2 種類の証人 (路と独立集合) と等号がどちらも現れ、かつ数秒で走る族。
#: reg3_12 は正則族の読み口 (shortcode + 次数の検査) を通すために足してある。
P0006_FAMILIES = ("graphs_06", "graphs_07", "reg3_12")
#: 2 種類の証人 (路と誘導木) と仮定成立グラフがどちらも現れる軽い族。
P0007_FAMILIES = ("graphs_06", "graphs_07", "reg3_12")
#: 等号 (内周 4) と奇内周のグラフがどちらも現れ、かつ数秒で走る族。
P0008_FAMILIES = ("graphs_06", "graphs_07", "reg3_12")
#: 等号 (C_6, K_{3,3}, C_7) と 3 つの帯がすべて現れ、かつ数秒で走る族。
P0009_FAMILIES = ("graphs_06", "graphs_07", "reg3_12")


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


# ----------------------------------------------------------------- p0006


@pytest.fixture()
def ham(tmp_path, monkeypatch):
    cert, prob, wdir = _prepare(P0006, P0006_FAMILIES, tmp_path, monkeypatch)
    fams = cert.data["families"]
    cert.data["totals"] = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "paths": sum(f["path_records"] for f in fams),
        "masks": sum(f["mask_records"] for f in fams),
        "hypothesis": sum(f["hypothesis_count"] for f in fams),
        "deep": sum(f["deep_hypothesis_count"] for f in fams),
        "classified": sum(f["count"] for f in fams if f["classified"]),
        "equality": sum(f["equality_count"] for f in fams),
        "counterexamples": len(cert.data["counterexamples"]),
    }
    return cert, prob, wdir


def _p0006_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0006_wowii194_hamiltonian import _verifier_source

    return list(_verifier_source(ck, fam))


def _p0006_blob(wdir, fam: dict) -> bytearray:
    return bytearray(gzip.decompress((wdir / fam["witness_file"]).read_bytes()))


def _p0006_rewrite(wdir, fam: dict, blob: bytearray) -> None:
    """証人を書き戻し、SHA-256 も辻褄を合わせる (ハッシュ検査を素通しする)."""
    import hashlib

    raw = gzip.compress(bytes(blob))
    (wdir / fam["witness_file"]).write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()


def _p0006_mode(blob: bytearray, index: int) -> int:
    return (blob[index >> 3] >> (7 - (index & 7))) & 1


def _p0006_first_path_index(blob: bytearray, fam: dict) -> int:
    """路の証人が付いている (= 仮定が成り立つ) 最初のグラフの番号."""
    return next(i for i in range(fam["count"]) if not _p0006_mode(blob, i))


def _p0006_lonely_equality(cert: Certificate):
    """論文の例に載っていない等号グラフを (族, g6) で返す.

    例に載っているグラフを隠すと ``eq_hit`` 側の検査が先に落ちてしまい、
    「等号リストが閉じているか」という本命の防御を試せない。
    """
    for fam in cert.data["families"]:
        if not fam["classified"] or not fam.get("equality_complete"):
            continue
        examples = set(fam.get("equality_examples", []))
        for g6 in fam.get("equality_graphs", []):
            if g6 not in examples:
                return fam, g6
    return None, None


def test_p0006_clean_certificate_verifies(ham):
    cert, prob, _ = ham
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0006_bit_flip_in_witness_is_detected(ham):
    cert, prob, wdir = ham
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0006_mode_bit_flipped_to_mask_is_detected(ham):
    r"""路の証人が付いたグラフを「仮定が破れる側」と偽ると必ず落ちる.

    モード 0 のグラフは仮定 $n\alpha \le n+S$ を満たすので、独立集合 $T$ が
    どれでも $n|T| \le n\alpha \le n+S$ となり、**どんなマスクを充てても**
    この検査は通らない。証人の種類の取り違えが原理的に隠せないことの確認。
    """
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    index = _p0006_first_path_index(blob, fam)
    blob[index >> 3] |= 1 << (7 - (index & 7))
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_empty_independent_set_witness_is_detected(ham):
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    at = fam["mode_bytes"] + fam["path_bytes"]
    blob[at:at + fam["mask_bytes"]] = bytes(fam["mask_bytes"])
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_too_small_independent_set_witness_is_detected(ham):
    """独立ではあるが小さすぎる証人 (1 頂点) は落ちる.

    独立性しか見ていない検証器はこれを通してしまう。上の空集合とは別の
    防御 (証人の**大きさ**) なので、独立に試す。
    """
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    at = fam["mode_bytes"] + fam["path_bytes"]
    blob[at:at + fam["mask_bytes"]] = (1).to_bytes(fam["mask_bytes"], "little")
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_inflated_independent_set_witness_is_detected(ham):
    """全頂点を証人だと言い張っても (独立でないので) 落ちる."""
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    at = fam["mode_bytes"] + fam["path_bytes"]
    full = (1 << fam["n"]) - 1
    blob[at:at + fam["mask_bytes"]] = full.to_bytes(fam["mask_bytes"], "little")
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_out_of_range_independent_set_witness_is_detected(ham):
    """存在しない頂点を含むマスクを弾く."""
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    at = fam["mode_bytes"] + fam["path_bytes"]
    blob[at:at + fam["mask_bytes"]] = \
        (1 << fam["n"]).to_bytes(fam["mask_bytes"], "little")
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_broken_path_witness_is_detected(ham):
    """路の証人を潰す (全頂点 0 の列) と、ハミルトン路の判定で落ちる."""
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    at = fam["mode_bytes"]
    width = (fam["n"] * fam["path_bits"] + 7) // 8
    blob[at:at + width] = bytes(width)
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "証人がハミルトン路でない" in _detail(report, "路の証人")


def test_p0006_dropped_mask_record_is_detected(ham):
    """独立集合の証人を 1 個削ると、長さの辻褄を合わせても落ちる."""
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    del blob[len(blob) - fam["mask_bytes"]:]
    fam["mask_records"] -= 1
    cert.data["totals"]["masks"] -= 1
    _p0006_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "独立集合の証人が仮定を破らない" in _detail(report, "路の証人")


def test_p0006_truncated_witness_file_is_detected(ham):
    """証人を後ろから削るだけなら、長さの検査で先に落ちる."""
    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    _p0006_rewrite(wdir, fam, _p0006_blob(wdir, fam)[:-1])
    report = prob.verify(cert)
    assert not report.ok
    assert "証人の長さが証明書と合わない" in _detail(report, "SHA-256")


def test_p0006_fabricated_counterexample_is_detected(ham):
    """反例を捏造すると、リストの非空検査だけでなく主張の再現でも落ちる."""
    import mar.checkgraph as ck

    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    blob = _p0006_blob(wdir, fam)
    index = _p0006_first_path_index(blob, fam)
    g = _p0006_graphs(fam)[index]
    alpha = ck.alpha_and_i(g)[0]
    lhs, rhs = ck.hamiltonian_hypothesis_sides(g, alpha)
    cert.data["counterexamples"].append(
        {"g6": ck.sets_to_graph6(g), "n": fam["n"], "family": fam["tag"],
         "alpha": alpha, "lhs": lhs, "rhs": rhs})
    cert.data["totals"]["counterexamples"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "反例の主張が再現しない" in _detail(report, "路の証人")


def test_p0006_hidden_equality_graph_is_detected(ham):
    """等号グラフを 1 個隠すと、そのグラフの再計算で露見する."""
    cert, prob, _ = ham
    fam, hidden = _p0006_lonely_equality(cert)
    assert hidden, "例に載っていない等号グラフが族に無いとテストにならない"
    fam["equality_graphs"].remove(hidden)
    fam["equality_count"] -= 1
    cert.data["totals"]["equality"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類する族")
    assert "等号リストに無い" in detail and hidden in detail


def test_p0006_false_equality_claim_is_detected(ham):
    """狭義で成り立つグラフを等号リストに入れると、厳密再計算で露見する."""
    import mar.checkgraph as ck

    cert, prob, _ = ham
    fam = _fam(cert, "graphs_06")
    listed = set(fam["equality_graphs"])
    innocent = None
    for g in _p0006_graphs(fam):
        g6 = ck.sets_to_graph6(g)
        if g6 in listed:
            continue
        lhs, rhs = ck.hamiltonian_hypothesis_sides(g, ck.alpha_and_i(g)[0])
        if lhs < rhs:
            innocent = g6
            break
    assert innocent, "狭義で成り立つグラフが族に無いとテストにならない"
    fam["equality_graphs"].append(innocent)
    fam["equality_count"] += 1
    cert.data["totals"]["equality"] += 1
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "分類する族")
    assert "等号リストにあるが等号でない" in detail and innocent in detail


def test_p0006_bogus_equality_example_is_detected(ham):
    """論文に載る等号グラフの例が等号リスト外なら不合格になる."""
    cert, prob, _ = ham
    fam = _fam(cert, "graphs_06")
    fam["equality_examples"] = ["E????"] + list(fam["equality_examples"])
    report = prob.verify(cert)
    assert not report.ok
    assert "等号リストに無いグラフが例に載っている" in _detail(report, "分類する族")


def test_p0006_incomplete_equality_list_is_not_reported_as_closed(ham):
    cert, prob, _ = ham
    _fam(cert, "graphs_06")["equality_complete"] = False
    report = prob.verify(cert)
    assert not report.ok
    assert "全リストがない" in _detail(report, "分類する族")


def test_p0006_inflated_equality_count_is_detected(ham):
    cert, prob, _ = ham
    _fam(cert, "graphs_06")["equality_count"] += 5
    cert.data["totals"]["equality"] += 5
    report = prob.verify(cert)
    assert not report.ok
    assert "等号の個数" in _detail(report, "分類する族")


def test_p0006_inflated_hypothesis_count_is_detected(ham):
    cert, prob, _ = ham
    _fam(cert, "graphs_06")["hypothesis_count"] += 1
    cert.data["totals"]["hypothesis"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "仮定成立数" in _detail(report, "走査したグラフ数")


def test_p0006_inflated_deep_count_is_detected(ham):
    """alpha >= 3 の内数 (論文の主張の中心) も独立に数え直される."""
    cert, prob, _ = ham
    _fam(cert, "graphs_06")["deep_hypothesis_count"] += 1
    cert.data["totals"]["deep"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "alpha >= 3 の個数" in _detail(report, "走査したグラフ数")


def test_p0006_inflated_totals_are_detected(ham):
    cert, prob, _ = ham
    cert.data["totals"]["deep"] += 7
    report = prob.verify(cert)
    assert not report.ok
    assert "deep" in _detail(report, "証明書の合計")


def test_p0006_wrong_published_count_is_detected(ham):
    cert, prob, _ = ham
    _fam(cert, "graphs_07")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0006_wrong_graph_count_is_detected(ham):
    """個数だけを水増しすると、走査個数の照合で落ちる.

    graphs_07 を選ぶのは 853 % 8 == 5 なので、1 増やしても ``mode_bytes`` が
    変わらないから。長さ検査が先に発火してしまうと、本命の個数照合を試せない。
    """
    cert, prob, _ = ham
    _fam(cert, "graphs_07")["count"] += 1
    cert.data["totals"]["graphs"] += 1
    cert.data["totals"]["classified"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "グラフ数" in _detail(report, "走査したグラフ数")


def _p0006_split(blob: bytearray, fam: dict):
    """証人ファイルを (モード列, 路レコード列, マスク列) に解く."""
    from mar.problems.p0006_wowii194_hamiltonian import _BitReader, _stream_bytes

    n, count = fam["n"], fam["count"]
    mode_bytes = (count + 7) // 8
    path_bits = fam["path_bits"]
    path_bytes = _stream_bytes(fam["path_records"] * n, path_bits)
    reader = _BitReader(bytes(blob[mode_bytes:mode_bytes + path_bytes]), path_bits)
    paths = [[reader.get() for _ in range(n)] for _ in range(fam["path_records"])]
    rest = blob[mode_bytes + path_bytes:]
    mb = fam["mask_bytes"]
    masks = [bytes(rest[i * mb:(i + 1) * mb]) for i in range(fam["mask_records"])]
    return bytearray(blob[:mode_bytes]), paths, masks


def _p0006_join(fam: dict, modes: bytearray, paths, masks) -> bytearray:
    """:func:`_p0006_split` の逆 (レコード数が変わっていてもよい)."""
    from mar.problems.p0006_wowii194_hamiltonian import _BitWriter

    writer = _BitWriter(fam["path_bits"])
    for rec in paths:
        for v in rec:
            writer.put(v)
    return bytearray(bytes(modes) + writer.getvalue() + b"".join(masks))


def test_p0006_deep_count_agrees_between_the_two_tiers(ham):
    """alpha >= 3 の内数は、分類の有無で数え方が変わっても一致する.

    分類する族は alpha を厳密に計算し、分類しない族は極大独立集合の列挙で
    「サイズ 3 以上があるか」だけを見る。実データでは分類しない族 (木) の
    仮定成立数が 0 なので後者の経路は一度も走らない。族を分類なしに落として
    走らせ、独立な 2 通りの数え方が同じ値を出すことを確かめる。
    """
    cert, prob, _ = ham
    fam = _fam(cert, "graphs_06")
    assert fam["classified"] and fam["hypothesis_count"] > 0
    tot = cert.data["totals"]
    tot["classified"] -= fam["count"]
    tot["equality"] -= fam["equality_count"]
    fam["classified"] = False
    fam["equality_count"] = 0
    fam["equality_graphs"] = []
    fam["equality_examples"] = []
    fam["equality_complete"] = False
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0006_relabelled_mask_with_real_path_is_detected(ham):
    """仮定が成り立たないグラフに本物のハミルトン路を付けても見破られる.

    モードビットを 1 -> 0 に倒し、独立集合の証人を捨てて、代わりに実在する
    ハミルトン路を差し込む。長さもレコード数も辻褄が合うので、形式的な検査は
    すべて素通りする。ここを止めるのは「分類する族では仮定の成否を検証器が
    自分で計算し直す」という一点だけなので、その防御を直接試している。
    """
    import itertools

    import mar.checkgraph as ck
    from mar.problems.p0006_wowii194_hamiltonian import _stream_bytes

    cert, prob, wdir = ham
    fam = _fam(cert, "graphs_06")
    n = fam["n"]
    blob = _p0006_blob(wdir, fam)
    graphs = _p0006_graphs(fam)
    modes, paths, masks = _p0006_split(blob, fam)

    # 仮定は破れている (モード 1) が、ハミルトン路自体は存在するグラフを探す。
    target = seq = None
    for i, g in enumerate(graphs):
        if _p0006_mode(blob, i):
            hit = next((p for p in itertools.permutations(range(n))
                        if ck.is_hamiltonian_path(g, list(p))), None)
            if hit is not None:
                target, seq = i, list(hit)
                break
    assert target is not None, "路をもつ反証グラフが族に無いとテストにならない"

    pos = sum(1 for j in range(target) if not _p0006_mode(blob, j))
    midx = sum(1 for j in range(target) if _p0006_mode(blob, j))
    paths.insert(pos, seq)
    del masks[midx]
    modes[target >> 3] &= ~(1 << (7 - (target & 7)))

    fam["path_records"] += 1
    fam["mask_records"] -= 1
    fam["hypothesis_count"] += 1
    fam["path_bytes"] = _stream_bytes(fam["path_records"] * n, fam["path_bits"])
    tot = cert.data["totals"]
    tot["paths"] += 1
    tot["masks"] -= 1
    tot["hypothesis"] += 1
    _p0006_rewrite(wdir, fam, _p0006_join(fam, modes, paths, masks))

    report = prob.verify(cert)
    assert not report.ok
    assert "仮定を満たさないのに仮定成立として数えられている" in \
        _detail(report, "分類する族")


# ----------------------------------------------------------------- p0007


@pytest.fixture()
def star(tmp_path, monkeypatch):
    cert, prob, wdir = _prepare(P0007, P0007_FAMILIES, tmp_path, monkeypatch)
    fams = cert.data["families"]
    cert.data["totals"] = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "paths": sum(f["path_records"] for f in fams),
        "masks": sum(f["mask_records"] for f in fams),
        "hypothesis": sum(f["hypothesis_count"] for f in fams),
        "deep": sum(f["deep_hypothesis_count"] for f in fams),
        "also194": sum(f["also194_count"] for f in fams),
        "counterexamples": len(cert.data["counterexamples"]),
    }
    return cert, prob, wdir


def _p0007_blob(wdir, fam: dict) -> bytearray:
    return bytearray(gzip.decompress((wdir / fam["witness_file"]).read_bytes()))


def _p0007_rewrite(wdir, fam: dict, blob: bytearray) -> None:
    import hashlib

    raw = gzip.compress(bytes(blob))
    (wdir / fam["witness_file"]).write_bytes(raw)
    fam["witness_sha256"] = hashlib.sha256(raw).hexdigest()


def _p0007_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0007_wowii200_star_tree import _verifier_source

    return list(_verifier_source(ck, fam))


def _p0007_split(blob: bytearray, fam: dict):
    """証人を (モードビット列, 路のリスト, マスクのリスト) にほどく."""
    from mar.problems.p0007_wowii200_star_tree import _BitReader

    n, mb = fam["n"], fam["mask_bytes"]
    head = fam["mode_bytes"]
    reader = _BitReader(bytes(blob[head:head + fam["path_bytes"]]),
                        fam["path_bits"])
    paths = [[reader.get() for _ in range(n)]
             for _ in range(fam["path_records"])]
    at = head + fam["path_bytes"]
    masks = [bytes(blob[at + k * mb:at + (k + 1) * mb])
             for k in range(fam["mask_records"])]
    return bytearray(blob[:head]), paths, masks


def _p0007_join(fam: dict, modes, paths, masks) -> bytearray:
    """:func:`_p0007_split` の逆 (証人を組み直す)."""
    from mar.problems.p0007_wowii200_star_tree import _BitWriter

    writer = _BitWriter(fam["path_bits"])
    for seq in paths:
        for v in seq:
            writer.put(v)
    return bytearray(bytes(modes) + writer.getvalue() + b"".join(masks))


def _p0007_first_path_index(blob: bytearray, fam: dict) -> int:
    """路の証人が付いている (= 仮定が成り立つ) 最初のグラフの番号."""
    return next(i for i in range(fam["count"])
                if not ((blob[i >> 3] >> (7 - (i & 7))) & 1))


def test_p0007_clean_certificate_verifies(star):
    cert, prob, _ = star
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0007_bit_flip_in_witness_is_detected(star):
    cert, prob, wdir = star
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0007_mode_bit_flipped_to_tree_is_detected(star):
    r"""路の証人が付いたグラフを「仮定が破れる側」と偽ると落ちる.

    モード 0 のグラフは $\mathrm{tree}(G) = t$ なので、位数 $t+1$ の誘導木は
    **そもそも存在しない**。どんなマスクを充てても検査は通らない。
    """
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    index = _p0007_first_path_index(blob, fam)
    blob[index >> 3] |= 1 << (7 - (index & 7))
    _p0007_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "誘導木の証人が閾値を超えない" in _detail(report, "路の証人")


def test_p0007_empty_tree_witness_is_detected(star):
    """空集合を誘導木の証人と称しても、位数が閾値を超えないので落ちる."""
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    at = fam["mode_bytes"] + fam["path_bytes"]
    blob[at:at + fam["mask_bytes"]] = bytes(fam["mask_bytes"])
    _p0007_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "誘導木の証人が閾値を超えない" in _detail(report, "路の証人")


def test_p0007_cyclic_witness_is_detected(star):
    """閾値を超える大きさでも、木でない (閉路をもつ) 集合は落ちる.

    位数だけを見る検証器はこれを通してしまう。誘導木性の検査が効いている
    ことの確認。
    """
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    # 閉路をもつ (= 木でない) モード 1 のグラフを 1 つ選び、その証人を
    # 全頂点集合に差し替える。位数 n > t は満たすが誘導部分グラフは G 自身で、
    # 閉路をもつので木ではない。
    graphs = _p0007_graphs(fam)
    rank = 0
    for i, g in enumerate(graphs):
        if not ((blob[i >> 3] >> (7 - (i & 7))) & 1):
            continue
        if sum(len(s) for s in g[1]) // 2 > fam["n"] - 1:
            break
        rank += 1
    else:                                    # pragma: no cover - 族の選び方の前提
        pytest.skip("閉路をもつモード 1 のグラフが族にない")
    at = fam["mode_bytes"] + fam["path_bytes"] + rank * fam["mask_bytes"]
    blob[at:at + fam["mask_bytes"]] = (
        ((1 << fam["n"]) - 1).to_bytes(fam["mask_bytes"], "little"))
    _p0007_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "誘導木の証人が閾値を超えない" in _detail(report, "路の証人")


def test_p0007_scrambled_path_is_detected(star):
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    at = fam["mode_bytes"]
    blob[at:at + fam["path_bytes"]] = bytes(fam["path_bytes"])
    _p0007_rewrite(wdir, fam, blob)
    report = prob.verify(cert)
    assert not report.ok
    assert "証人がハミルトン路でない" in _detail(report, "路の証人")


def test_p0007_inflated_also194_count_is_detected(star):
    """予想 194 との比較に使う内数を水増しすると落ちる."""
    cert, prob, _ = star
    _fam(cert, "graphs_06")["also194_count"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "予想 194 の仮定も満たす個数" in _detail(report, "走査したグラフ数")


def test_p0007_missing_hypothesis_graph_is_detected(star):
    """仮定を満たすグラフをリストから隠すと、分類が閉じない."""
    cert, prob, _ = star
    fam = _fam(cert, "graphs_06")
    examples = set(fam.get("hypothesis_examples", []))
    hidden = next(g6 for g6 in fam["hypothesis_graphs"] if g6 not in examples)
    fam["hypothesis_graphs"] = [g6 for g6 in fam["hypothesis_graphs"]
                                if g6 != hidden]
    fam["hypothesis_count"] -= 1
    cert.data["totals"]["hypothesis"] -= 1
    report = prob.verify(cert)
    assert not report.ok
    assert "が仮定リストに無い" in _detail(report, "モード 0 のグラフ")


def test_p0007_bogus_hypothesis_example_is_detected(star):
    """論文に載る例が仮定リスト外なら不合格になる."""
    cert, prob, _ = star
    fam = _fam(cert, "graphs_06")
    fam["hypothesis_examples"] = ["E????"] + fam["hypothesis_examples"]
    report = prob.verify(cert)
    assert not report.ok
    assert "仮定リストに無いグラフが例に載っている" in _detail(
        report, "モード 0 のグラフ")


def test_p0007_wrong_published_count_is_detected(star):
    """証明書が主張する公表値を書き換えると、検証器の表と食い違って落ちる."""
    cert, prob, _ = star
    _fam(cert, "graphs_07")["source_expected"] = 999
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0007_truncated_witness_file_is_detected(star):
    """証人を後ろから削るだけなら、長さの検査で先に落ちる."""
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    _p0007_rewrite(wdir, fam, _p0007_blob(wdir, fam)[:-1])
    report = prob.verify(cert)
    assert not report.ok
    assert "証人の長さが証明書と合わない" in _detail(report, "SHA-256")


def test_p0007_wrong_graph_count_is_detected(star):
    """走査個数を水増しすると、走査側と証人の総数の両方で辻褄が合わなくなる.

    graphs_07 を選ぶのは 853 % 8 == 5 なので、1 増やしても ``mode_bytes`` が
    変わらないから。長さ検査が先に発火すると本命の照合を試せない。
    """
    cert, prob, _ = star
    _fam(cert, "graphs_07")["count"] += 1
    cert.data["totals"]["graphs"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "グラフ数" in _detail(report, "走査したグラフ数")
    assert "証人の総数が走査個数に合わない" in _detail(report, "証明書の合計")


def test_p0007_inflated_totals_are_detected(star):
    """族ごとの集計と合わない合計 (論文の見出し数) は落とす."""
    cert, prob, _ = star
    cert.data["totals"]["masks"] += 3
    report = prob.verify(cert)
    assert not report.ok
    assert "masks" in _detail(report, "証明書の合計")


def test_p0007_inflated_hypothesis_count_is_detected(star):
    """仮定を満たす個数を水増しすると、モード 0 の実数と合わない."""
    cert, prob, _ = star
    _fam(cert, "graphs_06")["hypothesis_count"] += 1
    cert.data["totals"]["hypothesis"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "仮定成立数" in _detail(report, "走査したグラフ数")


def test_p0007_inflated_deep_count_is_detected(star):
    """完全グラフでない内数も検証器が数え直している."""
    cert, prob, _ = star
    _fam(cert, "graphs_06")["deep_hypothesis_count"] += 1
    cert.data["totals"]["deep"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "完全グラフでない個数" in _detail(report, "走査したグラフ数")


def test_p0007_hypothesis_list_marked_incomplete_is_detected(star):
    """上限に達していない族で全リストを省くと、分類が閉じたと主張できない."""
    cert, prob, _ = star
    fam = _fam(cert, "graphs_06")
    assert fam["hypothesis_count"] <= 200000, "上限未満の族でないと意味がない"
    fam["hypothesis_complete"] = False
    report = prob.verify(cert)
    assert not report.ok
    assert "上限に達していないのに" in _detail(report, "モード 0 のグラフ")


def test_p0007_fabricated_counterexample_is_detected(star):
    """反例を捏造すると、リストの非空検査だけでなく主張の再現でも落ちる."""
    import mar.checkgraph as ck

    from mar.problems.p0007_wowii200_star_tree import threshold

    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    index = _p0007_first_path_index(blob, fam)
    g = _p0007_graphs(fam)[index]
    t = threshold(fam["n"], ck.indep_neighbors_sum(g))
    cert.data["counterexamples"].append(
        {"g6": ck.sets_to_graph6(g), "n": fam["n"], "family": fam["tag"],
         "tree": t, "threshold": t})
    cert.data["totals"]["counterexamples"] += 1
    report = prob.verify(cert)
    assert not report.ok
    assert "反例の主張が再現しない" in _detail(report, "路の証人")


def test_p0007_borrowed_mask_from_another_graph_is_detected(star):
    """別のグラフの (それ自体は妥当な) 誘導木マスクを流用しても通らない.

    長さもレコード数も変わらないので、形式的な検査はすべて素通りする。
    止めているのは「そのグラフでちゃんと木を誘導しているか」の再計算だけ。
    """
    import mar.checkgraph as ck

    from mar.problems.p0007_wowii200_star_tree import threshold

    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    n = fam["n"]
    blob = _p0007_blob(wdir, fam)
    graphs = _p0007_graphs(fam)
    modes, paths, masks = _p0007_split(blob, fam)
    mode1 = [i for i in range(fam["count"])
             if (modes[i >> 3] >> (7 - (i & 7))) & 1]

    target = donor = None
    for rank, i in enumerate(mode1):
        g = graphs[i]
        t = threshold(n, ck.indep_neighbors_sum(g))
        for other, raw in enumerate(masks):
            if other == rank:
                continue
            subset = ck.mask_to_set(int.from_bytes(raw, "little"))
            if (max(subset, default=-1) >= n or len(subset) <= t
                    or not ck.induces_tree(g, subset)):
                target, donor = rank, other
                break
        if target is not None:
            break
    assert target is not None, "流用できないマスクが族に無いとテストにならない"

    masks[target] = masks[donor]
    _p0007_rewrite(wdir, fam, _p0007_join(fam, modes, paths, masks))
    report = prob.verify(cert)
    assert not report.ok
    assert "誘導木の証人が閾値を超えない" in _detail(report, "路の証人")


def test_p0007_out_of_range_mask_bit_is_detected(star):
    """位数を超える頂点番号を立てたマスクは受け付けない."""
    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    blob = _p0007_blob(wdir, fam)
    modes, paths, masks = _p0007_split(blob, fam)
    masks[0] = b"\xff" * fam["mask_bytes"]
    _p0007_rewrite(wdir, fam, _p0007_join(fam, modes, paths, masks))
    report = prob.verify(cert)
    assert not report.ok
    assert "誘導木の証人が閾値を超えない" in _detail(report, "路の証人")


def test_p0007_valid_permutation_that_is_not_a_path_is_detected(star):
    """頂点の置換としては正しいが辺を辿っていない列は落とす."""
    import itertools

    import mar.checkgraph as ck

    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    n = fam["n"]
    blob = _p0007_blob(wdir, fam)
    g = _p0007_graphs(fam)[_p0007_first_path_index(blob, fam)]
    modes, paths, masks = _p0007_split(blob, fam)
    bogus = next(list(p) for p in itertools.permutations(range(n))
                 if not ck.is_hamiltonian_path(g, list(p)))

    paths[0] = bogus
    _p0007_rewrite(wdir, fam, _p0007_join(fam, modes, paths, masks))
    report = prob.verify(cert)
    assert not report.ok
    assert "証人がハミルトン路でない" in _detail(report, "路の証人")


def test_p0007_mask_swapped_for_real_path_is_detected(star):
    """仮定が成り立たないグラフに本物のハミルトン路を付けても見破られる.

    モードビットを 1 -> 0 に倒し、誘導木の証人を捨てて実在するハミルトン路を
    差し込む。長さもレコード数も辻褄が合うので、止めているのは「モード 0 の
    グラフでは検証器が tree(G) を厳密に解き直す」という一点だけである。
    """
    import itertools

    import mar.checkgraph as ck

    from mar.problems.p0007_wowii200_star_tree import _stream_bytes

    cert, prob, wdir = star
    fam = _fam(cert, "graphs_06")
    n = fam["n"]
    blob = _p0007_blob(wdir, fam)
    graphs = _p0007_graphs(fam)
    modes, paths, masks = _p0007_split(blob, fam)

    target = seq = None
    for i, g in enumerate(graphs):
        if not (modes[i >> 3] >> (7 - (i & 7))) & 1:
            continue
        hit = next((p for p in itertools.permutations(range(n))
                    if ck.is_hamiltonian_path(g, list(p))), None)
        if hit is not None:
            target, seq = i, list(hit)
            break
    assert target is not None, "路をもつ反証グラフが族に無いとテストにならない"

    pos = sum(1 for j in range(target)
              if not (modes[j >> 3] >> (7 - (j & 7))) & 1)
    rank = sum(1 for j in range(target) if (modes[j >> 3] >> (7 - (j & 7))) & 1)
    paths.insert(pos, seq)
    del masks[rank]
    modes[target >> 3] &= ~(1 << (7 - (target & 7)))

    fam["path_records"] += 1
    fam["mask_records"] -= 1
    fam["hypothesis_count"] += 1
    fam["path_bytes"] = _stream_bytes(fam["path_records"] * n, fam["path_bits"])
    tot = cert.data["totals"]
    tot["paths"] += 1
    tot["masks"] -= 1
    tot["hypothesis"] += 1
    _p0007_rewrite(wdir, fam, _p0007_join(fam, modes, paths, masks))

    report = prob.verify(cert)
    assert not report.ok
    assert "仮定を満たさないのに仮定成立として数えられている" in \
        _detail(report, "モード 0 のグラフ")


# ----------------------------------------------------------------- p0008


@pytest.fixture()
def girth(tmp_path, monkeypatch):
    """p0008 を軽い 3 族に縮める.

    検証器は「族の取りこぼし」を検出するためにモジュールの宣言
    (``GRAPH_ORDERS`` 等) と証明書を突き合わせるので、宣言のほうも
    同じ 3 族に差し替えてから渡す。
    """
    mod = importlib.import_module(f"mar.problems.{P0008}")
    monkeypatch.setattr(mod, "GRAPH_ORDERS", [6, 7])
    monkeypatch.setattr(mod, "TREE_ORDERS", [])
    monkeypatch.setattr(mod, "REGULAR_FAMILIES", [(12, 3)])
    cert, prob, wdir = _prepare(P0008, P0008_FAMILIES, tmp_path, monkeypatch)
    _p0008_retotal(cert)
    return cert, prob, wdir


def _p0008_retotal(cert: Certificate) -> None:
    """縮めた族に合わせて合計を作り直す (合計の検査を素通しさせる)."""
    fams = cert.data["families"]
    cert.data["totals"] = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "equality": sum(f["counts"].get("equal", 0) for f in fams),
        "strict": sum(f["counts"].get("strict", 0) for f in fams),
        "counterexamples": sum(f["counts"].get("fail", 0) for f in fams),
        "exact_calls": sum(f["exact_calls"] for f in fams),
    }
    hist: dict[str, int] = {}
    for f in fams:
        for k, v in f.get("girth_hist", {}).items():
            hist[k] = hist.get(k, 0) + v
    cert.data["girth_totals"] = hist


def _p0008_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0008_wowii141_girth_tree import _verifier_source

    return list(_verifier_source(ck, fam))


def _p0008_lhs2(g) -> int:
    """検証器側の実装で左辺の 2 倍を求める."""
    import mar.checkgraph as ck
    from mar.problems.p0008_wowii141_girth_tree import _lmax, lhs_doubled

    return lhs_doubled(ck.girth(g), _lmax(ck, g))


def _p0008_equality(cert: Certificate):
    """等号グラフを 1 つ (族, graph6) で返す."""
    for fam in cert.data["families"]:
        for g6 in fam.get("equality_graphs", []):
            return fam, g6
    return None, None


def test_p0008_clean_certificate_verifies(girth):
    cert, prob, _ = girth
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0008_bit_flip_in_witness_is_detected(girth):
    cert, prob, wdir = girth
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0008_empty_witness_is_detected(girth):
    """空集合は木を誘導しない."""
    cert, prob, wdir = girth
    _rewrite_witness(wdir, _fam(cert, "graphs_06"), 0, 0)
    report = prob.verify(cert)
    assert not report.ok
    assert "T が木を誘導し" in _failed(report)


def test_p0008_witness_with_a_cycle_is_detected(girth):
    """閉路を含む頂点集合を証人にすると木の判定で落ちる."""
    import mar.checkgraph as ck

    cert, prob, wdir = girth
    fam = _fam(cert, "graphs_06")
    graphs = _p0008_graphs(fam)
    full = set(range(fam["n"]))
    index = next(i for i, g in enumerate(graphs) if not ck.induces_tree(g, full))
    _rewrite_witness(wdir, fam, index, (1 << fam["n"]) - 1)
    report = prob.verify(cert)
    assert not report.ok
    assert "T が木を誘導し" in _failed(report)


def test_p0008_too_small_witness_is_detected(girth):
    """木ではあるが下界に届かない証人 (1 頂点) を弾く.

    証人の**大きさ**を見ていない検証器はこれを通してしまうので、
    木かどうかの判定とは別に試す。
    """
    cert, prob, wdir = girth
    fam = _fam(cert, "graphs_06")
    graphs = _p0008_graphs(fam)
    index = next(i for i, g in enumerate(graphs) if _p0008_lhs2(g) > 2)
    _rewrite_witness(wdir, fam, index, 1)   # 頂点 0 だけ = 1 頂点の木
    report = prob.verify(cert)
    assert not report.ok
    assert "下界に届かない" in _detail(report, "T が木を誘導し")


def test_p0008_hidden_equality_graph_is_detected(girth):
    """等号グラフを 1 個隠すと、証人で狭義が閉じないことが露見する."""
    cert, prob, _ = girth
    fam, hidden = _p0008_equality(cert)
    assert hidden, "等号グラフが族に無いとテストにならない"
    fam["equality_graphs"].remove(hidden)
    fam["equality_data"].pop(hidden, None)
    fam["equality_examples"] = [g6 for g6 in fam["equality_examples"]
                                if g6 != hidden]
    fam["counts"]["equal"] -= 1
    fam["counts"]["strict"] += 1
    _p0008_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "等号")
    assert "等号リストに無いのに" in detail and hidden in detail


def test_p0008_false_equality_claim_is_detected(girth):
    """狭義成立のグラフを等号リストに入れると、厳密再計算で露見する."""
    import mar.checkgraph as ck

    cert, prob, _ = girth
    fam = _fam(cert, "graphs_06")
    listed = set(fam["equality_graphs"])
    innocent = next(g6 for g6 in (ck.sets_to_graph6(g)
                                  for g in _p0008_graphs(fam))
                    if g6 not in listed)
    fam["equality_graphs"].append(innocent)
    fam["counts"]["equal"] += 1
    fam["counts"]["strict"] -= 1
    _p0008_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "等号")
    assert "2*tree" in detail and innocent in detail


def test_p0008_tampered_equality_data_is_detected(girth):
    """等号グラフの 4 つ組 (girth, Delta, lmax, tree) を書き換えると落ちる."""
    cert, prob, _ = girth
    fam, g6 = _p0008_equality(cert)
    assert g6, "等号グラフが族に無いとテストにならない"
    fam["equality_data"][g6] = [4, 99, 99, 100]
    report = prob.verify(cert)
    assert not report.ok
    assert "等号データが再現しない" in _detail(report, "等号")


def test_p0008_dropped_family_is_detected(girth):
    """族を 1 つ落とした証明書は、残った族だけ見ると整合してしまう.

    公表値との突合も合計の検査も族ごとなので、走査範囲そのものを
    検査しないと「どこまで見たか」の主張だけが検証の外に残る。
    """
    cert, prob, _ = girth
    cert.data["families"] = [f for f in cert.data["families"]
                             if f["tag"] != "graphs_07"]
    _p0008_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    assert "graphs_07" in _detail(report, "走査範囲")


def test_p0008_wrong_girth_histogram_is_detected(girth):
    """内周の分布を 1 個ずらすと、検証器の数え直しと合わなくなる."""
    cert, prob, _ = girth
    fam = _fam(cert, "graphs_06")
    key = next(k for k, v in fam["girth_hist"].items() if v > 0)
    fam["girth_hist"][key] -= 1
    fam["girth_hist"]["9"] = fam["girth_hist"].get("9", 0) + 1
    _p0008_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    assert "内周の分布" in _failed(report)


def test_p0008_wrong_published_count_is_detected(girth):
    """証明書の期待個数を偽ると、検証器が自前で持つ公表値と食い違う."""
    cert, prob, _ = girth
    _fam(cert, "graphs_06")["source_expected"] = 111
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0008_inflated_totals_are_detected(girth):
    """合計だけ水増しした証明書 (論文の見出し数の偽装) を弾く."""
    cert, prob, _ = girth
    cert.data["totals"]["graphs"] += 1000
    report = prob.verify(cert)
    assert not report.ok
    assert "合計" in _failed(report)


# ----------------------------------------------------------------- p0009


@pytest.fixture()
def leafy(tmp_path, monkeypatch):
    """p0009 を軽い 3 族に縮める (走査範囲の宣言も同じ 3 族に差し替える)."""
    mod = importlib.import_module(f"mar.problems.{P0009}")
    monkeypatch.setattr(mod, "GRAPH_ORDERS", [6, 7])
    monkeypatch.setattr(mod, "TREE_ORDERS", [])
    monkeypatch.setattr(mod, "REGULAR_FAMILIES", [(12, 3)])
    cert, prob, wdir = _prepare(P0009, P0009_FAMILIES, tmp_path, monkeypatch)
    _p0009_retotal(cert)
    return cert, prob, wdir


def _p0009_retotal(cert: Certificate) -> None:
    """縮めた族に合わせて合計と帯の分布を作り直す."""
    fams = cert.data["families"]
    cert.data["totals"] = {
        "graphs": sum(f["count"] for f in fams),
        "families": len(fams),
        "equality": sum(f["counts"].get("equal", 0) for f in fams),
        "strict": sum(f["counts"].get("strict", 0) for f in fams),
        "counterexamples": sum(f["counts"].get("fail", 0) for f in fams),
        "bprime_counterexamples": len(cert.data.get("bprime_counterexamples",
                                                    [])),
        "bprime_equality": sum(f.get("bprime_equal", 0) for f in fams),
        "exact_calls": sum(f["exact_calls"] for f in fams),
    }
    hist: dict[str, int] = {}
    for f in fams:
        for k, v in f.get("zone_hist", {}).items():
            hist[k] = hist.get(k, 0) + v
    cert.data["zone_totals"] = hist


def _p0009_graphs(fam: dict):
    """検証器が読むのと同じ順序で族のグラフを返す."""
    import mar.checkgraph as ck
    from mar.problems.p0009_wowii2_leaf_local_indep import _verifier_source

    return list(_verifier_source(ck, fam))


def _p0009_need(g) -> int:
    """右辺 2S - 2n をテスト側で独立に計算する."""
    import mar.checkgraph as ck

    n, _ = g
    return 2 * ck.indep_neighbors_sum(g) - 2 * n


def _p0009_fmax(g) -> int:
    """f(G) = max_(uv in E) |N(u) 合併 N(v)| をテスト側で計算する."""
    import mar.checkgraph as ck

    _, nbr = g
    return max(len(nbr[u] | nbr[v]) for u, v in ck.edge_list(g))


def _p0009_connected_subset(g, core: set[int]) -> bool:
    """G[core] が連結か (検証器の実装を借りずに判定する)."""
    _, nbr = g
    if not core:
        return False
    start = next(iter(core))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in nbr[x] & core:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen == core


def _p0009_equality(cert: Certificate):
    """等号グラフを 1 つ (族, graph6) で返す."""
    for fam in cert.data["families"]:
        for g6 in fam.get("equality_graphs", []):
            return fam, g6
    return None, None


def test_p0009_clean_certificate_verifies(leafy):
    cert, prob, _ = leafy
    report = prob.verify(cert)
    assert report.ok, _failed(report)


def test_p0009_bit_flip_in_witness_is_detected(leafy):
    cert, prob, wdir = leafy
    _flip_first_byte(wdir / _fam(cert, "graphs_06")["witness_file"])
    report = prob.verify(cert)
    assert not report.ok
    assert "SHA-256" in _failed(report)


def test_p0009_empty_witness_is_detected(leafy):
    """葉 0 個の証人は (葉集合ではあるが) 下界に届かない."""
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    graphs = _p0009_graphs(fam)
    index = next(i for i, g in enumerate(graphs) if _p0009_need(g) > 0)
    _rewrite_witness(wdir, fam, index, 0)
    report = prob.verify(cert)
    assert not report.ok
    assert "下界に届かない" in _detail(report, "予想 2")


def test_p0009_witness_below_the_double_star_bound_is_detected(leafy):
    """右辺が 0 以下でも、定理 3.2 の下界を割る証人は別枠で弾く.

    予想 2 の不等式だけを見ている検証器はこれを通してしまう。論文が
    「証人は必ず二重星以上」と謳っている以上、そこも検査対象にする。
    """
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    graphs = _p0009_graphs(fam)
    index = next(i for i, g in enumerate(graphs)
                 if _p0009_need(g) <= 0 and _p0009_fmax(g) >= 3)
    _rewrite_witness(wdir, fam, index, 0)
    report = prob.verify(cert)
    assert not report.ok
    assert "二重星" in _detail(report, "定理 3.2 の機械照合")


def test_p0009_witness_with_empty_complement_is_detected(leafy):
    """全頂点を葉と主張する証人 (補集合が空) を弾く."""
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    _rewrite_witness(wdir, fam, 0, (1 << fam["n"]) - 1)
    report = prob.verify(cert)
    assert not report.ok
    assert "補集合が空" in _detail(report, "連結支配集合")


def test_p0009_witness_with_disconnected_core_is_detected(leafy):
    """補集合が連結でない証人 (全域木の葉集合になれない) を弾く."""
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    graphs = _p0009_graphs(fam)
    n = fam["n"]
    found = None
    for i, g in enumerate(graphs):
        for mask in range(1, 1 << n):
            core = {w for w in range(n) if not (mask >> w) & 1}
            if core and not _p0009_connected_subset(g, core):
                found = (i, mask)
                break
        if found:
            break
    assert found, "補集合が非連結になる証人を作れる族でないとテストにならない"
    _rewrite_witness(wdir, fam, found[0], found[1])
    report = prob.verify(cert)
    assert not report.ok
    assert "補集合が連結でない" in _detail(report, "連結支配集合")


def test_p0009_witness_with_out_of_range_vertex_is_detected(leafy):
    """存在しない頂点を立てた証人を弾く (ビット幅の検査)."""
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    _rewrite_witness(wdir, fam, 0, 1 << (fam["n"] + 1))
    report = prob.verify(cert)
    assert not report.ok
    assert "範囲外" in _detail(report, "連結支配集合")


def test_p0009_hidden_equality_graph_is_detected(leafy):
    """等号グラフを 1 個隠すと、証人で狭義が閉じないことが露見する."""
    cert, prob, _ = leafy
    fam, hidden = _p0009_equality(cert)
    assert hidden, "等号グラフが族に無いとテストにならない"
    fam["equality_graphs"].remove(hidden)
    fam["equality_data"].pop(hidden, None)
    fam["equality_examples"] = [g6 for g6 in fam["equality_examples"]
                                if g6 != hidden]
    fam["counts"]["equal"] -= 1
    fam["counts"]["strict"] += 1
    _p0009_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "等号")
    assert "等号リストに無いのに" in detail and hidden in detail


def test_p0009_false_equality_claim_is_detected(leafy):
    """狭義成立のグラフを等号リストに入れると、証人の大きさで露見する."""
    import mar.checkgraph as ck

    cert, prob, _ = leafy
    fam = _fam(cert, "graphs_06")
    listed = set(fam["equality_graphs"])
    innocent = next(g6 for g6 in (ck.sets_to_graph6(g)
                                  for g in _p0009_graphs(fam))
                    if g6 not in listed)
    fam["equality_graphs"].append(innocent)
    fam["counts"]["equal"] += 1
    fam["counts"]["strict"] -= 1
    _p0009_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "等号")
    assert "等号リストにあるが" in detail and innocent in detail


def test_p0009_phantom_equality_data_is_detected(leafy):
    """等号リストに無いグラフを等号データに紛れ込ませると落ちる.

    論文の等号表は ``equality_data`` を読むので、ここが等号リストと
    ずれていると「検証済み」と書かれた行が検査を素通りしてしまう。
    """
    import mar.checkgraph as ck

    cert, prob, _ = leafy
    fam = _fam(cert, "graphs_06")
    listed = set(fam["equality_graphs"])
    phantom = next(g6 for g6 in (ck.sets_to_graph6(g)
                                 for g in _p0009_graphs(fam))
                   if g6 not in listed)
    fam["equality_data"][phantom] = [2, 12, 2, 4]
    report = prob.verify(cert)
    assert not report.ok
    detail = _detail(report, "等号")
    assert "等号リスト外" in detail and phantom in detail


def test_p0009_witness_path_outside_the_directory_is_detected(leafy):
    """証人の置き場所を証明書に指定させない (パストラバーサルの遮断)."""
    cert, prob, wdir = leafy
    fam = _fam(cert, "graphs_06")
    shutil.copy2(wdir / fam["witness_file"],
                 wdir.parent / fam["witness_file"])
    fam["witness_file"] = f"../{fam['witness_file']}"
    report = prob.verify(cert)
    assert not report.ok
    assert "規約と違う" in _detail(report, "SHA-256")


def test_p0009_absurd_witness_record_count_is_detected(leafy):
    """証人の個数を桁違いに大きく主張しても、展開前に頭打ちで弾く."""
    cert, prob, _ = leafy
    _fam(cert, "graphs_06")["witness_records"] = 10 ** 9
    report = prob.verify(cert)
    assert not report.ok
    assert "範囲外" in _detail(report, "SHA-256")


def test_p0009_tampered_equality_data_is_detected(leafy):
    """等号グラフの 4 つ組 (葉数, S, Delta, f) を書き換えると落ちる."""
    cert, prob, _ = leafy
    fam, g6 = _p0009_equality(cert)
    assert g6, "等号グラフが族に無いとテストにならない"
    fam["equality_data"][g6] = [fam["equality_data"][g6][0], 99, 99, 99]
    report = prob.verify(cert)
    assert not report.ok
    assert "等号データが再現しない" in _detail(report, "等号")


def test_p0009_dropped_family_is_detected(leafy):
    """族を 1 つ落とした証明書 (走査範囲の偽装) を弾く."""
    cert, prob, _ = leafy
    cert.data["families"] = [f for f in cert.data["families"]
                             if f["tag"] != "graphs_07"]
    _p0009_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    assert "graphs_07" in _detail(report, "走査範囲")


def test_p0009_wrong_zone_histogram_is_detected(leafy):
    """帯 (trivial / delta / hard) の分布を 1 個ずらすと落ちる.

    帯は論文の主定理 5.1 が「予想を閉じた割合」の根拠なので、証人と
    独立に数え直していないと見出しの数字だけ偽装できてしまう。
    """
    cert, prob, _ = leafy
    fam = _fam(cert, "graphs_06")
    key = next(k for k, v in fam["zone_hist"].items() if v > 0)
    fam["zone_hist"][key] -= 1
    fam["zone_hist"]["hard" if key != "hard" else "trivial"] = (
        fam["zone_hist"].get("hard" if key != "hard" else "trivial", 0) + 1)
    _p0009_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    assert "帯" in _failed(report)


def test_p0009_wrong_bprime_equality_count_is_detected(leafy):
    """予想 B' の等号数を偽ると、検証器の数え直しと合わなくなる."""
    cert, prob, _ = leafy
    fam = _fam(cert, "graphs_06")
    fam["bprime_equal"] += 1
    _p0009_retotal(cert)
    report = prob.verify(cert)
    assert not report.ok
    assert "B' の等号数" in _detail(report, "B'")


def test_p0009_wrong_published_count_is_detected(leafy):
    """証明書の期待個数を偽ると、検証器が自前で持つ公表値と食い違う."""
    cert, prob, _ = leafy
    _fam(cert, "graphs_06")["source_expected"] = 111
    report = prob.verify(cert)
    assert not report.ok
    assert "公表値" in _failed(report)


def test_p0009_inflated_totals_are_detected(leafy):
    """合計だけ水増しした証明書 (論文の見出し数の偽装) を弾く."""
    cert, prob, _ = leafy
    cert.data["totals"]["graphs"] += 1000
    report = prob.verify(cert)
    assert not report.ok
    assert "合計" in _failed(report)
