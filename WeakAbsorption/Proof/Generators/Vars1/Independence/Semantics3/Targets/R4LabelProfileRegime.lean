import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4SnapshotData
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4RowProfileFamily

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Current audited R4 label-sector classifier.

At the current audited R4 universe, `regime` factors through the
target-label sector.  The present classifier inspects the label-sector
object; in fact, for the current catalog it is already determined by
the `state` component.
-/
def regimeOfLabels : ObservedTargetLabels → ObservedRegime
  | ⟨_, _, .bridge_split⟩ => .bridgeSplit
  | _                    => .pure

theorem observedRegime_factors_through_labels
    (tg : ObservedTarget) :
    observedRegime tg =
      regimeOfLabels (observedLabels tg) := by
  cases tg <;> native_decide

theorem observedSnapshot_regime_factors
    (tg : ObservedTarget) :
    (observedSnapshot tg).regime =
      regimeOfLabels (observedSnapshot tg).labels := by
  simpa [observedSnapshot] using
    observedRegime_factors_through_labels tg

/--
Conceptual quotient theorem:
on the current audited R4 universe, regime depends only on target labels.
-/
theorem observedRegime_eq_of_labels_eq
    {tg₁ tg₂ : ObservedTarget}
    (h :
      (observedSnapshot tg₁).labels =
      (observedSnapshot tg₂).labels) :
    observedRegime tg₁ = observedRegime tg₂ := by
  calc
    observedRegime tg₁
        = regimeOfLabels (observedSnapshot tg₁).labels := by
            simpa using observedSnapshot_regime_factors tg₁
    _   = regimeOfLabels (observedSnapshot tg₂).labels := by
            simp [h]
    _   = observedRegime tg₂ := by
            simpa using (observedSnapshot_regime_factors tg₂).symm

/--
R4 snapshot reconstructed from:
- target-label sector
- target-level regime as a function of labels
- row-geometry sector
- shape family as a function of rowProfile
-/
theorem observedSnapshot_eq_reconstructed
    (tg : ObservedTarget) :
    observedSnapshot tg =
      { labels := observedLabels tg
        regime := regimeOfLabels (observedLabels tg)
        geometry := observedGeometry tg
        shapeFamily := shapeFamilyOfProfile (observedGeometry tg).rowProfile } := by
  unfold observedSnapshot
  rw [observedRegime_factors_through_labels tg]
  rw [observedGeometry_shapeFamily_factors tg]

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
