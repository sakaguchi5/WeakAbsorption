/-!
`Semantics2` の最上位契約。

目的:
- `Semantics2` は `Necessity` フリーな clean-room を作るための新しい意味論フォルダである。
- 例外として、再現目標を固定する `Targets/` と、比較監査を行う `Audit/` は `Necessity` を参照してよい。
- `Clean/` は `Necessity` 参照禁止。
- `Public/CleanOnly` は clean-room 利用者向けの唯一の入口。
- 旧 `Semantics/` は移行期間中だけ残す。後で削除する。

依存規約:
- `Targets/`   : `Necessity` 参照可。
- `Audit/`     : `Necessity` 参照可。ただし `Clean/` から import 禁止。
- `Clean/`     : `Necessity` 参照禁止。`Targets/` と `Core/` だけを見る。
- `Public/`    : 入口整理専用。

運用方針:
- まず `Targets/R4ObservedTarget.lean` に再現目標を固定する。
- その後 `Clean/Instances/R4/*` をゼロベースで再構築する。
- 旧 `Semantics/Instances/R4/*` は参照元・比較元としてのみ扱い、移植先ではない。
-/
