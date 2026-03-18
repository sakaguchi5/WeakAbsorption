/-
本ファイルは上位研究メモであり、現時点では formal theorem / definition を置く場所ではない。

配置先を `WeakAbsorption/Proof/Notes/` とした理由:
- 内容が `Generators/Vars1` の局所事情に閉じず、
  primitive shortcut, tower shortcut, reuse shortcut, nonexistence strategy,
  statement design など広域の証明設計に関わるため。
- 研究メモは今後も増え続けるため、末端ディレクトリではなく
  上位に集約する必要があるため。

本来の最終配置先:
- 将来的には内容に応じて
  `WeakAbsorption/Proof/Generators/...`
  `WeakAbsorption/Proof/Classification/...`
  あるいは shortcut 専用の formal 層
  へ分解・移設する想定である。

このファイルでは、将来の Lean 定義・定理化のために、
paper-level の仮説・候補分類・失敗例・否定戦略を
日本語で凍結して残す。
-/

/-
# Vars1 shortcut 研究メモ

## 1. 現時点で確定したこと

DoubleSq 型 witness は isolated な一発現象ではなく、
repeated-squaring tower 上の family に一般化された。
したがって、二重塔は新しい独立 pressure source の証拠というより、
既存 closure が最初に可視化される最小の高さである可能性が高い。

この観点では、DoubleSq は core generator というより
shortcut family の代表元と読む方が自然である。

## 2. 本メモでの shortcut の暫定的意味

formal definition はまだ固定しないが、ここでは shortcut family を
「既存 core relation の closure の中にある正規形どうしの relation で、
自然数パラメータに関して一様に書ける圧縮 law」
として考える。

primitive shortcut family とは、
より小さい shortcut family の反復合成として理解するのが不自然な
最小単位を指す。

## 3. repetition 側の予測

repetition pressure から来る primitive shortcut family の本命は
tower-drop family である。

理由:
- repeated-squaring tower は自己相似再帰を持つ
- 高さという自然な rank がある
- predecessor law を一様に書ける

現時点では、repetition 側の他の自然候補は
tower-drop の文脈化・合成・変形に還元される可能性が高い。

## 4. reuse 側の候補分類と現時点の予測

自然な one-parameter recursion 候補として、少なくとも次を検討した。

A. 片側伸長型
   B_{n+1} = B_n ⋆ z, p ⋆ B_n など
   → 左内部埋め込みの形が段ごとにずれやすく、
     uniform predecessor law が立ちにくい。

B. 自己複製型
   B_{n+1} = B_n ⋆ B_n
   → 一様 law は立ちやすいが、
     本質的には repetition / tower 側の grammar に吸収されやすい。
     genuinely new reuse family とは言いにくい。

C. ネスト再利用型
   B_{n+1} = p ⋆ (B_n ⋆ z) など
   → depth 2,3 の時点で、
     collapse の主語が B_n / B_{n-1} / ... の間で競合しやすい。
     その結果、clean な predecessor law が壊れやすい。

以上より、reuse 側には isolated witness はありえても、
tower に対応する clean な one-parameter primitive shortcut family は
存在しないか、存在しても tower family の文脈化に還元される可能性が高い。

## 5. 現時点の最善予測

primitive shortcut family は repetition 側では tower-drop family が本命であり、
reuse 側には tower に対応する clean な対称物は無い、
あるいは tower disguise に還元される。

## 6. 将来 Lean に持ち込むときの theorem candidate

(1) repetition 側 existence:
    tower-drop family は shortcut family として存在する。

(2) repetition 側 uniqueness 予想:
    natural repetition shortcut family は tower-drop に尽きる。

(3) reuse 側 nonexistence 予想:
    natural unary nested-reuse grammar 上には、
    tower disguise を除いて uniform predecessor shortcut family は存在しない。

本メモは上記の予測を paper-level で凍結するためのものであり、
現時点では定義・定理・証明を固定しない。
-/
