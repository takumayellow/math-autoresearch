"""PDF のページを PNG に落とす (組版の目視確認用).

使い方: python tools/pdf2png.py papers/pXXXX/main.pdf [出力ディレクトリ] [--dpi 110]
"""

from __future__ import annotations

import sys
from pathlib import Path

import fitz  # PyMuPDF


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 1
    pdf = Path(argv[0])
    out = Path(argv[1]) if len(argv) > 1 and not argv[1].startswith("--") else pdf.parent / "preview"
    dpi = 110
    if "--dpi" in argv:
        dpi = int(argv[argv.index("--dpi") + 1])
    out.mkdir(parents=True, exist_ok=True)
    doc = fitz.open(pdf)
    for i, page in enumerate(doc, 1):
        pix = page.get_pixmap(dpi=dpi)
        path = out / f"page{i:02d}.png"
        pix.save(path)
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
