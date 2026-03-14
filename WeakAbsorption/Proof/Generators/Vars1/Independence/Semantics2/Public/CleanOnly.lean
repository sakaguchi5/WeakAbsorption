import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Contract
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Core.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Targets.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Clean.Main

/-!
clean-room 利用者向けの唯一の入口。

この入口を使う理由:
- `Targets/` は再現目標として見える。
- `Clean/` は実装として見える。
- `Audit/` は見えないので、old comparison に引きずられない。
-/
