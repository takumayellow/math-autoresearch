# math-autoresearch (`mar`)

数学の未解決問題に対して **探索 → 有限証明書 → 独立検証 → 日本語論文 (LaTeX/PDF)**
を一本のコマンドで回すための研究自動化パイプライン。

```
python -m mar list                       # 問題一覧
python -m mar new p0004_xxx "タイトル"   # 新しい問題の雛形 (2 ファイル) を作る
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
data/witnesses/      証人のサイドカー (バイナリ)
papers/<problem_id>/ main.tex / main.pdf / preview/*.png
tools/pdf2png.py     組版の目視確認用
docs/methodology.md  研究自動化の方法論と、実際に踏んだ落とし穴
```

## 環境

- Python 3.10 + sympy / numpy / networkx (探索側のみ)
- TinyTeX (`lualatex`, jlreq, luatexja, 原ノ味フォント)
- PDF 目視確認に PyMuPDF (`pip install pymupdf`)

## 現在の問題

| ID | 種別 | 内容 | 規模 | 結果 |
|----|------|------|------|------|
| `p0000_jacobian_2026` | 追試 | 2026 年のヤコビアン予想反例の独立検証 + 一般ファイバーの決定 | — | 反例を再現、一般ファイバーを決定 |
| `p0001_txgraffiti_i_mustar` | 未解決 | 正則グラフの独立支配数と飽和数 ($i \le \mu^*$, TxGraffiti 予想 3) | 連結正則グラフ 155,033 個 | 反例なし、等号 3,651 個 |
| `p0002_txgraffiti_zf_alpha` | 未解決 | 亜立方体グラフのゼロ強制数と独立数 ($Z \le \alpha+1$, TxGraffiti 予想 2) | $\Delta \le 3$ ($n \le 10$) + 立方体 ($n \le 18$) 計 48,524 個 | 反例なし、等号 46 個 |
| `p0003_saturation_harmonic` | 追試 + 拡張 | 飽和数と調和指数 ($\mu^* \le H$, TxGraffiti 予想 4, 反証済み) の反例の完全分類 | 連結グラフ $n \le 10$ + 木 $n \le 20$ | 反例を完全列挙 |

### 証人つき証明書 (p0002 以降)

$Z$, $\alpha$, $\mu^*$ はいずれも計算が NP 困難なので、「探索器の計算を検証器が
やり直す」設計だと検証が探索と同じだけ高価になる。片側の不等式に限れば、
これは**証人**で回避できる:

| 主張 | 証人 | 検証コスト |
|------|------|-----------|
| $Z(G) \le \alpha(G)+1$ | 独立集合 $A$ + ゼロ強制集合 $S$ ($|S| \le |A|+1$) | 線形 |
| $\mu^*(G) \le H(G)$ | 極大マッチング $M$ ($|M| \le H(G)$) | 線形 |

証人は列挙順に並べたバイナリのサイドカー (`data/witnesses/`) に置き、
その SHA-256 を証明書 JSON に記録する。

逆向きの主張 (反例であること、等号が成立すること、最大値がいくつか) は
片側評価だけでは閉じない。これらは次の 2 つの型で閉じる
(詳細は `docs/methodology.md`):

- **例外リスト方式** — 逆向きが要る対象を漏れなく証明書に列挙し、そこだけ
  検証器が厳密計算する。残りは証人が強い側の不等式 (`|S| <= |A|`) を満たす
  ことで排除する。族の大きさによらず分類全体が閉じる。
- **上下から挟む** — 最大値は「証人による全数の上界」と「達成グラフ 1 個の
  厳密再計算による下界」が一致することで確定する。

網羅性の照合に使う公表値 (OEIS A001349 / A000055 / A002851) は、
探索器の表ではなく検証器が独自にもつ定数を使う。
