"""問題ごとの見出し (手書きしてよい唯一の部分).

**見出しに数値を書かない。** 走査したグラフ数・等号の個数・反例の個数と
いった数は証明書の ``claim`` からそのまま引く (:mod:`mar.announce.compose`)。
見出しは「何をしたか」だけを言う。証明書が更新されて数が変わっても、
見出しは書き換えなくてよい — この分担を崩すと、論文で禁じている
「手打ちの数値」が投稿文に忍び込む。

1 通目に入りきらなかった claim の続きは、返信 (スレッド) に回る。
"""

from __future__ import annotations

from dataclasses import dataclass

BASE_TAGS = ("#数学", "#グラフ理論")


@dataclass(frozen=True)
class Highlight:
    headline: str
    tags: tuple[str, ...] = BASE_TAGS


HIGHLIGHTS: dict[str, Highlight] = {
    "p0000_jacobian_2026": Highlight(
        "ヤコビアン予想の反例 (2026 年公表) を独立に検証した",
        tags=("#数学", "#代数幾何")),
    "p0001_txgraffiti_i_mustar": Highlight(
        "TxGraffiti 予想 3 を、正則グラフの完全リストで網羅検証した"),
    "p0002_txgraffiti_zf_alpha": Highlight(
        "TxGraffiti 予想 2 を、証人つきで網羅検証した"),
    "p0003_saturation_harmonic": Highlight(
        "TxGraffiti 予想 4 は偽だった。反例を有限範囲で完全に分類した"),
    "p0004_wowii61_induced_forest": Highlight(
        "Graffiti.pc の WOWII 予想 61 を、証人つきで網羅検証した"),
    "p0005_wowii_induced_tree": Highlight(
        "WOWII 予想 142・144・146 を同時に網羅検証した"),
    "p0006_wowii194_hamiltonian": Highlight(
        "WOWII 予想 194 (ハミルトン路の十分条件) を網羅検証した"),
    "p0007_wowii200_star_tree": Highlight(
        "WOWII 予想 200 の最小反例の位数を確定し、反例の無限族を証明した"),
    "p0008_wowii141_girth_tree": Highlight(
        "WOWII 予想 141 を証明した。等号成立グラフも特徴づけた"),
    "p0009_wowii2_leaf_local_indep": Highlight(
        "WOWII 予想 2 に二重星定理を与え、より強い予想も検証した"),
    "p0010_wowii_ls_lower_bounds": Highlight(
        "WOWII 予想 172 は偽だった。反例の無限族を与えた"),
    "p0011_wowii_tree_lower_bounds": Highlight(
        "WOWII 予想 72・76・84・85 (誘導木の下界) を網羅検証した"),
    "p0012_wowii19_bipartite_avg_ecc": Highlight(
        "WOWII 予想 19 を解決した。証明と証人つきの網羅検証を与えた"),
    "p0013_wowii_ls_plus_b_bounds": Highlight(
        "WOWII 予想 176 と 181 は偽だった。反例の無限族を与えた"),
    "p0014_wowii_forest_number_bounds": Highlight(
        "WOWII の森数の下界予想を、証人つきで網羅検証した"),
}


def highlight(problem_id: str) -> Highlight:
    try:
        return HIGHLIGHTS[problem_id]
    except KeyError:
        raise KeyError(
            f"{problem_id} の見出しが未登録。"
            f"mar/announce/highlights.py に追記する。") from None
