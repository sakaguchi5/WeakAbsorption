import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4CompressedSnapshotAudit
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4AtomAudit
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4LabelCompressionLimit

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Row-geometry sector picture on the current audited R4 catalog.

Interpretation:
- `rowProfile` is sufficient to recover the current row-geometry observables.
- the coarser observables below it do not suffice to recover `rowProfile`.
-/
theorem row_geometry_current_picture :
    (∀ tg : ObservedTarget,
      observedRowShape tg = (observedRowProfile tg).support)
    ∧
    (∀ tg : ObservedTarget,
      observedAtomCount tg = (observedRowProfile tg).atomCount)
    ∧
    (∀ tg : ObservedTarget,
      observedShapeCount tg = (observedRowProfile tg).shapeCount)
    ∧
    (∀ tg : ObservedTarget,
      observedShapeFamily tg = shapeFamilyOfProfile (observedRowProfile tg))
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedRowShape tg₁ = observedRowShape tg₂
      ∧ observedShapeFamily tg₁ ≠ observedShapeFamily tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedShapeFamily tg₁ = observedShapeFamily tg₂
      ∧ observedRowProfile tg₁ ≠ observedRowProfile tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedShapeFamily tg₁ = observedShapeFamily tg₂
      ∧ observedAtomCount tg₁ = observedAtomCount tg₂
      ∧ observedShapeCount tg₁ = observedShapeCount tg₂
      ∧ observedRowProfile tg₁ ≠ observedRowProfile tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedAtomCount tg₁ = observedAtomCount tg₂
      ∧ observedShapeCount tg₁ = observedShapeCount tg₂
      ∧ observedShapeFamily tg₁ ≠ observedShapeFamily tg₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tg
    exact observedRowShape_factors_through_rowProfile tg
  · intro tg
    exact observedAtomCount_factors_through_rowProfile tg
  · intro tg
    exact observedShapeCount_factors_through_rowProfile tg
  · intro tg
    exact observedShapeFamily_factors_through_rowProfile tg
  · exact rowShape_does_not_determine_shapeFamily
  · exact shapeFamily_does_not_determine_rowProfile
  · exact shapeFamily_and_counts_do_not_determine_rowProfile
  · exact counts_do_not_determine_shapeFamily

/--
Atom/refinement picture on the current audited R4 catalog.

Interpretation:
- exact-row atom data forgets to `rowProfile`;
- this forgetful map is genuinely many-to-one;
- `rowProfile` does not determine the label-side sector.
-/
theorem atom_refinement_current_picture :
    (∀ tg : ObservedTarget,
      rowProfileOfAtoms (Necessity.rowAtomsOfTarget tg) = observedRowProfile tg)
    ∧
    (∃ a₁ a₂ : Necessity.RowAtom,
      a₁ ≠ a₂ ∧ atomToShapeCoord a₁ = atomToShapeCoord a₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedRowProfile tg₁ = observedRowProfile tg₂
      ∧ observedLabels tg₁ ≠ observedLabels tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedRowProfile tg₁ = observedRowProfile tg₂
      ∧ observedState tg₁ ≠ observedState tg₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tg
    exact rowProfileOfTargetAtoms_eq_observedRowProfile tg
  · exact rowProfile_is_a_genuine_quotient.2
  · refine ⟨.nfXADecorRightPred, .nfXADecorLeftPred, ?_, ?_⟩
    · exact same_rowProfile_different_labels.1
    · exact same_rowProfile_different_labels.2
  · refine ⟨.nfXADecorRightPred, .nfXADecorLeftPred, ?_, ?_⟩
    · exact same_rowProfile_different_state.1
    · exact same_rowProfile_different_state.2

/--
Label-side picture on the current audited R4 catalog.

Interpretation:
- `kernel`, `shell`, `regime` are all too coarse on their own;
- `state` and `(kernel, shell)` are equivalent coordinates;
- so the current label-side sector has not yet been genuinely compressed.
-/
theorem label_side_current_summary :
    (∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedKernel tg₁ = observedKernel tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedShell tg₁ = observedShell tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedRegime tg₁ = observedRegime tg₂)
    ∧
    Function.Injective observedKernelShell
    ∧
    Function.Injective observedState
    ∧
    (∀ {tg₁ tg₂ : ObservedTarget},
      observedState tg₁ = observedState tg₂ ↔
        (observedKernel tg₁ = observedKernel tg₂ ∧
         observedShell tg₁ = observedShell tg₂))
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedKernel tg₁ = observedKernel tg₂
      ∧ observedRegime tg₁ = observedRegime tg₂
      ∧ tg₁ ≠ tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedShell tg₁ = observedShell tg₂
      ∧ observedRegime tg₁ = observedRegime tg₂
      ∧ tg₁ ≠ tg₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact observedKernel_not_injective
  · exact observedShell_not_injective
  · exact observedRegime_not_injective
  · exact observedKernelShell_injective
  · exact observedState_injective
  · intro tg₁ tg₂
    exact observedState_eq_iff_kernelShell_eq
  · exact kernel_and_regime_do_not_determine_target
  · exact shell_and_regime_do_not_determine_target

/--
Compressed-snapshot picture on the current audited R4 catalog.

Interpretation:
- the audited R4 snapshot factors through the compressed image
  `(state, rowProfile)`;
- on the current audited catalog, this compressed image still separates
  targets and observed snapshots.
-/
theorem compressed_snapshot_current_picture :
    (∀ tg : ObservedTarget,
      reconstruct (compressedSnapshot tg) = observedSnapshot tg)
    ∧
    Function.Injective compressedSnapshot
    ∧
    Function.Injective observedSnapshot
    ∧
    (∀ {tg₁ tg₂ : ObservedTarget},
      compressedSnapshot tg₁ = compressedSnapshot tg₂ →
        observedSnapshot tg₁ = observedSnapshot tg₂)
    ∧
    (∀ {tg₁ tg₂ : ObservedTarget},
      observedState tg₁ = observedState tg₂ →
      observedRowProfile tg₁ = observedRowProfile tg₂ →
        tg₁ = tg₂)
    ∧
    (∀ {tg₁ tg₂ : ObservedTarget},
      observedLabels tg₁ = observedLabels tg₂ →
      observedGeometry tg₁ = observedGeometry tg₂ →
        tg₁ = tg₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tg
    exact reconstruct_compressedSnapshot tg
  · exact compressedSnapshot_injective
  · exact observedSnapshot_injective
  · intro tg₁ tg₂ h
    exact compressedSnapshot_eq_implies_observedSnapshot_eq h
  · intro tg₁ tg₂ hs hp
    exact state_and_rowProfile_determine_target hs hp
  · intro tg₁ tg₂ hl hg
    exact labels_and_geometry_determine_target hl hg

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
