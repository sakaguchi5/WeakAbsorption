import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4SnapshotData

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Current audited R4 row-profile classifier.

This is intentionally catalog-level, not a final general theory.
Its job is to witness that the row-geometry sector of current audited R4
factors through `observedRowProfile`.
-/
def shapeFamilyOfProfile : ObservedRowProfile → ObservedShapeFamily
  | ⟨[(_, 1)]⟩ => .singleton
  | ⟨[(_, 2)]⟩ => .sameCoordDuplication
  | ⟨[(c₁, 1), (c₂, 1)]⟩ =>
      if c₁.side = .root ∧ c₂.side = .root then
        .rootMixedPure
      else
        .bridgeSplitMixed
  | _ => .singleton

theorem observedShapeFamily_factors_through_rowProfile
    (tg : ObservedTarget) :
    observedShapeFamily tg =
      shapeFamilyOfProfile (observedRowProfile tg) := by
  cases tg <;> native_decide

theorem observedSnapshot_shapeFamily_factors
    (tg : ObservedTarget) :
    (observedSnapshot tg).shapeFamily =
      shapeFamilyOfProfile (observedSnapshot tg).rowProfile := by
  simpa [observedSnapshot] using
    observedShapeFamily_factors_through_rowProfile tg

theorem observedRowShape_factors_through_rowProfile
    (tg : ObservedTarget) :
    observedRowShape tg =
      (observedRowProfile tg).support := by
  rfl

theorem observedAtomCount_factors_through_rowProfile
    (tg : ObservedTarget) :
    observedAtomCount tg =
      (observedRowProfile tg).atomCount := by
  rfl

theorem observedShapeCount_factors_through_rowProfile
    (tg : ObservedTarget) :
    observedShapeCount tg =
      (observedRowProfile tg).shapeCount := by
  rfl

theorem observedGeometry_rowProfile
    (tg : ObservedTarget) :
    (observedGeometry tg).rowProfile =
      observedRowProfile tg := by
  rfl

theorem observedGeometry_shapeFamily_factors
    (tg : ObservedTarget) :
    observedShapeFamily tg =
      shapeFamilyOfProfile (observedGeometry tg).rowProfile := by
  simpa [observedGeometry] using
    observedShapeFamily_factors_through_rowProfile tg

theorem observedGeometry_rowShape_factors
    (tg : ObservedTarget) :
    (observedGeometry tg).rowShape =
      (observedGeometry tg).rowProfile.support := by
  rfl

theorem observedGeometry_atomCount_factors
    (tg : ObservedTarget) :
    (observedGeometry tg).atomCount =
      (observedGeometry tg).rowProfile.atomCount := by
  rfl

theorem observedGeometry_shapeCount_factors
    (tg : ObservedTarget) :
    (observedGeometry tg).shapeCount =
      (observedGeometry tg).rowProfile.shapeCount := by
  rfl

/--
Conceptual quotient theorem:
on the current audited R4 universe, shape family depends only on row profile.
-/
theorem observedShapeFamily_eq_of_rowProfile_eq
    {tg₁ tg₂ : ObservedTarget}
    (h :
      (observedGeometry tg₁).rowProfile =
      (observedGeometry tg₂).rowProfile) :
    observedShapeFamily tg₁ = observedShapeFamily tg₂ := by
  calc
    observedShapeFamily tg₁
        = shapeFamilyOfProfile (observedGeometry tg₁).rowProfile := by
            simpa using observedGeometry_shapeFamily_factors tg₁
    _   = shapeFamilyOfProfile (observedGeometry tg₂).rowProfile := by
            simp [h]
    _   = observedShapeFamily tg₂ := by
            simpa using (observedGeometry_shapeFamily_factors tg₂).symm

/--
Row-geometry sector of the snapshot is reconstructed from `rowProfile`
plus `shapeFamily` as a quotient of `rowProfile`.
-/
theorem observedSnapshot_geometrySector_eq_reconstructed
    (tg : ObservedTarget) :
    (observedSnapshot tg).geometry = observedGeometry tg ∧
    (observedSnapshot tg).shapeFamily =
      shapeFamilyOfProfile (observedGeometry tg).rowProfile := by
  constructor
  · rfl
  · simpa [observedSnapshot] using
      observedGeometry_shapeFamily_factors tg

theorem same_rowShape_different_shapeFamily :
    observedRowShape .nfXASqRightPred =
      observedRowShape .nfXASqAPred
    ∧
    observedShapeFamily .nfXASqRightPred ≠
      observedShapeFamily .nfXASqAPred := by
  decide

theorem rowShape_does_not_determine_shapeFamily :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedRowShape tg₁ = observedRowShape tg₂ ∧
      observedShapeFamily tg₁ ≠ observedShapeFamily tg₂ := by
  refine ⟨.nfXASqRightPred, .nfXASqAPred, ?_, ?_⟩
  · rfl
  · decide

theorem same_shapeFamily_different_rowProfile :
    observedShapeFamily .nfUHolePred =
      observedShapeFamily .nfUDecorHolePred
    ∧
    observedRowProfile .nfUHolePred ≠
      observedRowProfile .nfUDecorHolePred := by
  decide

theorem shapeFamily_does_not_determine_rowProfile :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedShapeFamily tg₁ = observedShapeFamily tg₂ ∧
      observedRowProfile tg₁ ≠ observedRowProfile tg₂ := by
  refine ⟨.nfUHolePred, .nfUDecorHolePred, ?_, ?_⟩
  · rfl
  · decide

theorem same_shapeFamily_and_counts_different_rowProfile :
    observedShapeFamily .nfUHolePred =
      observedShapeFamily .nfUDecorHolePred
    ∧
    observedAtomCount .nfUHolePred =
      observedAtomCount .nfUDecorHolePred
    ∧
    observedShapeCount .nfUHolePred =
      observedShapeCount .nfUDecorHolePred
    ∧
    observedRowProfile .nfUHolePred ≠
      observedRowProfile .nfUDecorHolePred := by
  decide

theorem shapeFamily_and_counts_do_not_determine_rowProfile :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedShapeFamily tg₁ = observedShapeFamily tg₂ ∧
      observedAtomCount tg₁ = observedAtomCount tg₂ ∧
      observedShapeCount tg₁ = observedShapeCount tg₂ ∧
      observedRowProfile tg₁ ≠ observedRowProfile tg₂ := by
  refine ⟨.nfUHolePred, .nfUDecorHolePred, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · decide

theorem same_counts_different_shapeFamily :
    observedAtomCount .nfUHolePred =
      observedAtomCount .nfUDecorRightPred
    ∧
    observedShapeCount .nfUHolePred =
      observedShapeCount .nfUDecorRightPred
    ∧
    observedShapeFamily .nfUHolePred ≠
      observedShapeFamily .nfUDecorRightPred := by
  decide

theorem counts_do_not_determine_shapeFamily :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedAtomCount tg₁ = observedAtomCount tg₂ ∧
      observedShapeCount tg₁ = observedShapeCount tg₂ ∧
      observedShapeFamily tg₁ ≠ observedShapeFamily tg₂ := by
  refine ⟨.nfUHolePred, .nfUDecorRightPred, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
