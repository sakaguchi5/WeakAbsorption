import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics2.Targets.R4ObservedSnapshot

/-!
`Semantics2` における R4 の再現目標アンカー。

役割:
- 新 clean-room が再現すべき target-level 観測値を固定する唯一の入口。
- ここだけは `Necessity` を参照してよい。

移行の第一歩:
- 現在は旧 `Semantics/Instances/R4/R4KernelObservedSpec.lean` を source of truth として参照する。
- 後で旧 `Semantics/` を削除する前に、ここへ最小核を移植する。

ここに最終的に残すべき内容:
- `ObservedShapeFamily`
- `ObservedKernelSnapshot`
- `observedKernel`
- `observedShell`
- `observedState`
- `observedRegime`
- `observedRowAtoms`
- `observedRowShape`
- `observedShapeFamily`
- `observedSnapshot`

ここに最終的に置かないもの:
- `package_*_matches_observed` のような監査補題
- `Hypergraph` や `Shape` の派生 catalog
- old comparison の束

実務上の意味:
- clean-room は最初、このファイルだけを「再現相手」として扱う。
- 旧 `System/Package/Shape/Hypergraph` は参考実装であって再現目標そのものではない。
-/
