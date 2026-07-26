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
#: 元データの走査が軽く、かつ等号グラフを含む族。
P0002_FAMILIES = ("subcubic_06", "subcubic_08")
#: 反例は $n \ge 9$ にしか無いので、ここで検査するのは比と証人の側。
P0003_FAMILIES = ("graphs_06", "graphs_07")


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
    partner = blob[0] - 1          # 先頭グラフの頂点 0 の相手
    assert partner >= 0
    blob[0] = 0                    # 辺を 1 本外す -> 極大性が壊れる
    blob[partner] = 0
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
