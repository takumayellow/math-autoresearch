"""証人サイドカーを**再現可能な**バイト列として書くためのヘルパ.

`gzip.open(path, "wb")` は gzip ヘッダの MTIME フィールドに「今の時刻」を
書き込む。中身が 1 バイトも変わらなくても、走らせ直せばファイルの SHA-256 は
毎回変わる。証明書は証人ファイルの SHA-256 を持っているので、これでは

- 探索を走らせ直して同じ証人が出たことを、ハッシュで確かめられない
- 証明書を書き換えずに証人だけ作り直す、という運用ができない

という不都合がある (実際 p0008 で、走査後に小さいテスト用の探索が
`graphs_06` / `graphs_07` の証人を上書きし、中身は同一なのに SHA-256 が
食い違って検証が FAIL した)。

MTIME を 0 に固定すると、同じ探索器・同じ入力からは**同じバイト列**が出る。

書き込みはプロセスごとの一時ファイルに対して行い、最後に `os.replace` で
差し替える。同じ族を 2 つのプロセスが同時に書いても (レビュー用の再走査を
本走査と並行して回した、など)、出来上がるのはどちらか一方の完全なファイル
であって、両者が混ざった壊れたファイルにはならない。実際に、走査中の
`p0010_graphs_10` を別プロセスが `open(path, "wb")` で開き直したために
291,176 バイトのゼロ穴が空いたことがある。
"""
from __future__ import annotations

import gzip
import os
from contextlib import contextmanager
from pathlib import Path
from typing import BinaryIO, Iterator


@contextmanager
def open_witness(path: Path, compresslevel: int = 9) -> Iterator[BinaryIO]:
    """証人サイドカーを書くための gzip ストリームを開く (MTIME = 0).

    `gzip.open(path, "wb")` の置き換え。ヘッダは MTIME 以外そのままなので、
    出来上がるファイルは通常の gzip として読める。gzip ヘッダに載せる名前は
    一時ファイル名ではなく**最終的なファイル名**なので、途中経過に依存せず
    同じバイト列になる。
    """
    tmp = path.with_name(f"{path.name}.{os.getpid()}.part")
    try:
        with open(tmp, "wb") as raw:
            with gzip.GzipFile(filename=path.name, mode="wb", fileobj=raw,
                               compresslevel=compresslevel, mtime=0) as out:
                yield out
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            tmp.unlink()
