"""証人サイドカーがバイト単位で再現可能であることの回帰テスト.

証明書は証人ファイルの SHA-256 を持つ。`gzip.open(path, "wb")` は
gzip ヘッダに書き込み時刻を埋めるので、中身が同一でも走らせ直すと
ハッシュが変わってしまう (p0008 で実際に踏んだ: 走査後に小さいテスト用の
探索が同じ族の証人を上書きし、中身は同一なのに検証が SHA-256 不一致で
FAIL した)。`mar.search.witness.open_witness` は MTIME を 0 に固定する。
"""
from __future__ import annotations

import gzip
import hashlib
import struct
import time

from mar.search.witness import open_witness

PAYLOAD = [struct.pack("<I", i * 7919 % 2**32) for i in range(1000)]


def _write(path) -> str:
    with open_witness(path) as out:
        for chunk in PAYLOAD:
            out.write(chunk)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_same_content_same_hash(tmp_path):
    """時刻をまたいで書いても同じバイト列になる."""
    a = _write(tmp_path / "w.bin.gz")
    time.sleep(1.1)                     # MTIME が 1 秒以上ずれる状況を作る
    b = _write(tmp_path / "w.bin.gz")
    assert a == b


def test_mtime_field_is_zero(tmp_path):
    """gzip ヘッダの MTIME (4-8 バイト目) が 0 で固定されている."""
    path = tmp_path / "w.bin.gz"
    _write(path)
    head = path.read_bytes()[:10]
    assert head[:2] == b"\x1f\x8b"                       # gzip マジック
    assert struct.unpack("<I", head[4:8])[0] == 0


def test_still_plain_gzip(tmp_path):
    """普通の gzip として読める (検証器は gzip.decompress で読む)."""
    path = tmp_path / "w.bin.gz"
    _write(path)
    assert gzip.decompress(path.read_bytes()) == b"".join(PAYLOAD)


def test_different_content_different_hash(tmp_path):
    """内容が変われば当然ハッシュも変わる (テストが何も見ていない事故の防止)."""
    path = tmp_path / "w.bin.gz"
    a = _write(path)
    with open_witness(path) as out:
        for chunk in PAYLOAD[:-1]:
            out.write(chunk)
    assert hashlib.sha256(path.read_bytes()).hexdigest() != a


def test_stream_closed_after_block(tmp_path):
    """with を抜けた時点でファイルが閉じている (追記されない)."""
    path = tmp_path / "w.bin.gz"
    with open_witness(path) as out:
        out.write(b"x" * 10)
    assert out.closed
    size = path.stat().st_size
    assert size > 0 and path.read_bytes()[:2] == b"\x1f\x8b"
