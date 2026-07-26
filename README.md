# math-autoresearch (`mar`)

数学の未解決問題に対して **探索 → 有限証明書 → 独立検証 → 日本語論文 (LaTeX/PDF)**
を一本のコマンドで回すための研究自動化パイプライン。

```
python -m mar list                       # 問題一覧
python -m mar survey  p0000_jacobian_2026   # 先行研究ゲート (未解決性の根拠)
python -m mar search  p0001_xxx --budget 600
python -m mar verify  --all              # 全証明書を独立に再検査
python -m mar paper   p0001_xxx          # 日本語 PDF を生成
python -m mar run     p0001_xxx          # search → verify → paper
```

## 設計原則

1. **主張は有限証明書に落とす。** 結果とは「対象 (JSON)」と「検証手続き」の 2 つ組。
   浮動小数点数は証明書に入れない (整数・有理数・代数的数のみ)。
2. **検証器は探索器と実装を共有しない。** 探索は SymPy / NumPy を使ってよいが、
   検証は `mar.exact` (標準ライブラリの `Fraction` だけで書いた多項式環・剰余環) を使う。
   共有バグが検証をすり抜けるのを防ぐため。
3. **先行研究ゲート。** `Problem.survey` に「この日付時点で未解決」と言える出典が
   なければ探索を実行しない (`mar search` が拒否する)。計算探索の最大の失敗は
   誤りではなく *既知の結果の再発見*。
4. **検証に落ちた証明書は論文化しない。** `mar paper` は verify を再実行し、
   1 つでも FAIL があれば PDF を作らない。
5. **数値は本文に直書きしない。** 論文本文は証明書 JSON から生成する
   (`paper_sections`)。人手で書いた数字と実際の計算結果がずれる事故を構造的に防ぐ。

## ディレクトリ

```
src/mar/
  certificate.py     証明書 (JSON) と再現メタデータ
  exact.py           検証専用の厳密演算 (多変数多項式環, QQ[z]/(g), 無平方判定)
  problem.py         Problem インタフェース + レジストリ
  __main__.py        CLI
  problems/          1 問題 1 モジュール (pNNNN_*.py), 本文は _pNNNN_paper.py
  search/            探索エンジン (グラフ列挙など)
  report/            LaTeX 生成 (jlreq + luatexja + 原ノ味フォント, lualatex)
data/certificates/   証明書 JSON
papers/<problem_id>/ main.tex / main.pdf / preview/*.png
tools/pdf2png.py     組版の目視確認用
```

## 環境

- Python 3.10 + sympy / numpy / networkx (探索側のみ)
- TinyTeX (`lualatex`, jlreq, luatexja, 原ノ味フォント)
- PDF 目視確認に PyMuPDF (`pip install pymupdf`)

## 現在の問題

| ID | 種別 | 内容 |
|----|------|------|
| `p0000_jacobian_2026` | 追試 | 2026 年のヤコビアン予想反例の独立検証 + 一般ファイバーの決定 |
