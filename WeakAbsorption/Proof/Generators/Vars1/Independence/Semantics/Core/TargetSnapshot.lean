import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Observed.Policy
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Observed.Core.TargetIndex

/-
このファイルは「target ごとの凍結観測値そのもの」を置く場所。
ここで持つのは target-indexed な観測値だけで、catalog や old bridge や整合性証明は混ぜない。

ここに残すべき本体:
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

現在 `R4KernelObservedSpec.lean` からここへ移す対象:
- target ごとの kernel / shell / state / regime の frozen 値
- target ごとの exact-row atoms の frozen 値
- target ごとの row shape の frozen 値
- target ごとの shape family の frozen 値
- それらを束ねた snapshot record

ここに置かないもの:
- `observedVertexCount` は `Observed/Catalog/VertexUniverse.lean`
- `observedDistinctEdgeSupportCount` は `Observed/Catalog/SupportCatalog.lean`
- `package_kernel_matches_observed` などの old 依存照合定理は `Observed/Bridge/TargetSnapshotToOld.lean`
- `observedRowAtoms_sound` / `observedRowShape_sound` は `Observed/Coherence/TargetSnapshotCoherence.lean`
- `observedShapeFamily_sound` は `Observed/Coherence/FamilyClassification.lean`

この段階で追加しておくべき観点:
- `observedRowAtoms` と `observedRowShape` は source of truth としてここに一元化する。
- `ShapeCatalog` 側には「distinct representatives と target から catalog 代表への対応」だけを置き、
  row shape の値そのものを二重保持しない。
- `SupportCatalog` 側にも support の distinct representatives は置くが、
  target ごとの row atoms の値そのものはここを正本にする。
-/
