/-!
`Semantics3` の最上位契約。

目的:
- `Semantics3` は snapshot-first な再構築入口である。
- 第1段階では target-label sector と row-geometry sector を分けて固定する。
- row-geometry sector の中核は `ObservedRowProfile` とする。
- `rowAtoms` は第1段階の public contract には入れない。
- comparison theorem / audit theorem はここには置かない。

設計方針:
- `Core/` は clean observed language だけを持つ。
- `Targets/` は現時点の監査済み R4 snapshot data を固定する。
- `Clean/` は今は薄い placeholder とし、再構築本体は後で積む。
- `Public/CleanOnly` は clean-side 利用者向けの入口。
- `Targets/` は source-of-truth だが、最終的にはさらに圧縮されうる。
-/
