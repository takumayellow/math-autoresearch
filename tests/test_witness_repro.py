"""証人サイドカーがバイト単位で再現可能であることの回帰テスト.

証明書は証人ファイルの SHA-256 を持つ。`gzip.open(path, "wb")` は
gzip ヘッダに書き込み時刻を埋めるので、中身が同一でも走らせ直すと
ハッシュが変わってしまう (p0008 で実際に踏んだ: 走査後に小さいテスト用の
探索が同じ族の証人を上書きし、中身は同一なのに検証が SHA-256 不一致で
FAIL した)。`mar.search.witness.open_witness` は MTIME を 0 に固定する。

あわせて書き込みの原子性も見る。証人は一時ファイルに書いてから
`os.replace` で差し替えるので、走査中のファイルを別プロセスが開き直しても
中身が混ざらない (p0010 で 291,176 バイトのゼロ穴が空いた事故の回帰)。
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


def test_writes_through_a_private_temp_file(tmp_path):
    """書いている最中の中身は最終パスに現れない (別プロセスが踏めない)."""
    path = tmp_path / "w.bin.gz"
    old = _write(path)
    seen = []
    with open_witness(path) as out:
        out.write(b"y" * 4096)
        seen.append(hashlib.sha256(path.read_bytes()).hexdigest())
        parts = [p.name for p in tmp_path.iterdir() if p.name.endswith(".part")]
        assert parts, "一時ファイルが作られていない"
    assert seen == [old]                       # 途中では古い内容のまま
    assert hashlib.sha256(path.read_bytes()).hexdigest() != old
    assert not [p for p in tmp_path.iterdir() if p.name.endswith(".part")]


def test_failed_write_leaves_the_old_file_intact(tmp_path):
    """途中で落ちたら差し替えない。一時ファイルも残さない."""
    path = tmp_path / "w.bin.gz"
    old = _write(path)
    try:
        with open_witness(path) as out:
            out.write(b"z" * 4096)
            raise RuntimeError("走査が途中で落ちた")
    except RuntimeError:
        pass
    assert hashlib.sha256(path.read_bytes()).hexdigest() == old
    assert not [p for p in tmp_path.iterdir() if p.name.endswith(".part")]
