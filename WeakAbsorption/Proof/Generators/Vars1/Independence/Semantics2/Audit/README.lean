/-!
`Audit/` は old 実装との比較・監査専用層。

ここでは `Necessity` や旧 `Semantics` を参照してよい。
ただし `Clean/` から import してはいけない。

役割:
- clean-room 実装が再現目標に一致しているかを後で証明する。
- 旧 `PackageBridge` や comparison 補題の受け皿になる。
-/
