import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Targets.R4ObservedTarget
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.R4KernelObservedSpec
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.PackageBridge
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Shape
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Hypergraph

/-!
このファイルに残すべき内容:
- `Targets/R4ObservedTarget.lean` が旧 `R4KernelObservedSpec.lean` と一致することの監査補題。
- 旧 `PackageBridge`・`Shape`・`Hypergraph` が target anchor とどう対応していたかの比較メモ。

ここに置くものの例:
- `observedSnapshot` が旧 package / row / shape / support と一致する、という comparison theorem 群。

注意:
- これは clean-room の一部ではない。
- ここに厚い比較補題を集めて、`Clean/` を汚染しない。
-/
