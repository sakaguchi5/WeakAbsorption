import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Hypergraph
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowShape

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Instances
namespace R4

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore
open Core

section PackageBridge

abbrev PackageRowShapeCoord := R4System.Shape

/-- Package-indexed row-shape: forget tags and keep only slot × channel incidence. -/
def packageRowShape (tg : CoreKernelTarget) : List PackageRowShapeCoord :=
  (r4SystemPackage tg).shape

/-- Package projection agrees extensionally with the original target-indexed row-shape. -/
theorem packageRowShape_eq_old (tg : CoreKernelTarget) :
    packageRowShape tg = rowShapeOfTarget tg := by
  have hPkgObs : packageRowShape tg = observedRowShape tg := by
    simpa [packageRowShape] using r4System_shape_matches_observed tg
  have hObsOld : observedRowShape tg = rowShapeOfTarget tg :=
    (rowShape_matches_observed tg).symm
  exact hPkgObs.trans hObsOld

theorem packageRegime_eq_old (tg : CoreKernelTarget) :
    (r4SystemPackage tg).regime = packageRegime tg := by
  exact (r4System_regime_matches_observed tg).trans (package_regime_matches_observed tg).symm

theorem packageIsTwoAtom_iff_old (tg : CoreKernelTarget) :
    PackageIsTwoAtom tg ↔ IsTwoAtom tg := by
  constructor
  · intro h
    change (packageEdgeSupport tg).length = 2 at h
    rw [packageEdgeSupport_eq_old tg] at h
    exact h
  · intro h
    change (packageEdgeSupport tg).length = 2
    rw [packageEdgeSupport_eq_old tg]
    exact h

theorem packageIsOneAtom_iff_old (tg : CoreKernelTarget) :
    PackageIsOneAtom tg ↔ IsOneAtom tg := by
  constructor
  · intro h
    change (packageEdgeSupport tg).length = 1 at h
    rw [packageEdgeSupport_eq_old tg] at h
    exact h
  · intro h
    change (packageEdgeSupport tg).length = 1
    rw [packageEdgeSupport_eq_old tg]
    exact h

theorem packageRowShape_mem_iff_old (tg : CoreKernelTarget) (sc : RowShapeCoord) :
    sc ∈ packageRowShape tg ↔ sc ∈ rowShapeOfTarget tg := by
  simp [packageRowShape_eq_old tg]

theorem packageRowShape_length_eq_old (tg : CoreKernelTarget) :
    (packageRowShape tg).length = (rowShapeOfTarget tg).length := by
  simp [packageRowShape_eq_old tg]

theorem packageRowShape_eq_iff_old (tg : CoreKernelTarget) (sh : List RowShapeCoord) :
    packageRowShape tg = sh ↔ rowShapeOfTarget tg = sh := by
  simp [packageRowShape_eq_old tg]

theorem packageRegime_system_iff_package (tg : CoreKernelTarget) (r : CoreKernelRegime) :
    (r4SystemPackage tg).regime = r ↔ packageRegime tg = r := by
  simp [packageRegime_eq_old tg]

-- Backward-compatible alias.
theorem packageRegime_iff_old (tg : CoreKernelTarget) (r : CoreKernelRegime) :
    (r4SystemPackage tg).regime = r ↔ packageRegime tg = r :=
  packageRegime_system_iff_package tg r

theorem packageAllRoot_iff_old (tg : CoreKernelTarget) :
    (∀ sc, sc ∈ packageRowShape tg → sc.2 = CtxChannel.root) ↔
    (∀ sc, sc ∈ rowShapeOfTarget tg → sc.2 = CtxChannel.root) := by
  constructor <;> intro h sc hsc
  · exact h sc ((packageRowShape_mem_iff_old tg sc).2 hsc)
  · exact h sc ((packageRowShape_mem_iff_old tg sc).1 hsc)

theorem packageRootChannel_mem_iff_old (tg : CoreKernelTarget) (sc : RowShapeCoord) :
    (sc ∈ packageRowShape tg -> sc.2 = CtxChannel.root) ↔
    (sc ∈ rowShapeOfTarget tg -> sc.2 = CtxChannel.root) := by
  constructor <;> intro h hsc
  · exact h ((packageRowShape_mem_iff_old tg sc).2 hsc)
  · exact h ((packageRowShape_mem_iff_old tg sc).1 hsc)

end PackageBridge

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
