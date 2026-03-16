import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4SnapshotData
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4RowProfileFamily
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4LabelProfileRegime

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Current audited R4 kernel classifier from state.

Mathematical meaning:
- on the current audited R4 catalog, `state` is finer than `kernel`.
-/
def kernelOfState : ObservedState → ObservedKernelClass
  | .saRight               => .saKernel
  | .saLeftLift            => .saKernel
  | .decorRight_right      => .decorRightKernel
  | .decorRight_leftLift   => .decorRightKernel
  | .decorLeft_right       => .decorLeftKernel
  | .decorLeft_leftLift    => .decorLeftKernel
  | .stable_leftLift       => .stableKernel
  | .hole_root             => .holeKernel
  | .decorHole_root        => .decorHoleKernel
  | .aa_right              => .aaKernel
  | .aa_leftLift           => .aaKernel
  | .bridge_split          => .bridgeKernel

/--
Current audited R4 shell classifier from state.

Mathematical meaning:
- on the current audited R4 catalog, `state` is finer than `shell`.
-/
def shellOfState : ObservedState → ObservedShellKind
  | .saRight               => .rightShell
  | .saLeftLift            => .leftLift
  | .decorRight_right      => .rightShell
  | .decorRight_leftLift   => .leftLift
  | .decorLeft_right       => .rightShell
  | .decorLeft_leftLift    => .leftLift
  | .stable_leftLift       => .leftLift
  | .hole_root             => .rootShell
  | .decorHole_root        => .rootShell
  | .aa_right              => .rightShell
  | .aa_leftLift           => .leftLift
  | .bridge_split          => .bridgeSplitShell

/--
Current audited R4 regime classifier from state.

Mathematical meaning:
- on the current audited R4 catalog, `state` is also finer than `regime`.
-/
def regimeOfState : ObservedState → ObservedRegime
  | .bridge_split => .bridgeSplit
  | _             => .pure

/--
Target-label sector reconstructed from state alone.

This is catalog-level compression, not yet a Core-level law.
-/
def labelsOfState (st : ObservedState) : ObservedTargetLabels :=
  { kernel := kernelOfState st
    shell := shellOfState st
    state := st }

theorem observedKernel_factors_through_state
    (tg : ObservedTarget) :
    observedKernel tg = kernelOfState (observedState tg) := by
  cases tg <;> native_decide

theorem observedShell_factors_through_state
    (tg : ObservedTarget) :
    observedShell tg = shellOfState (observedState tg) := by
  cases tg <;> native_decide

theorem observedLabels_factors_through_state
    (tg : ObservedTarget) :
    observedLabels tg = labelsOfState (observedState tg) := by
  unfold observedLabels labelsOfState
  rw [observedKernel_factors_through_state tg]
  rw [observedShell_factors_through_state tg]

theorem observedRegime_factors_through_state
    (tg : ObservedTarget) :
    observedRegime tg = regimeOfState (observedState tg) := by
  cases tg <;> native_decide

theorem observedSnapshot_labels_factors
    (tg : ObservedTarget) :
    (observedSnapshot tg).labels = labelsOfState (observedState tg) := by
  simpa [observedSnapshot] using
    observedLabels_factors_through_state tg

theorem observedSnapshot_regime_factors_through_state
    (tg : ObservedTarget) :
    (observedSnapshot tg).regime = regimeOfState (observedState tg) := by
  simpa [observedSnapshot] using
    observedRegime_factors_through_state tg

/--
Conceptual quotient theorem:
on the current audited R4 universe, the whole target-label sector depends only on `state`.
-/
theorem observedLabels_eq_of_state_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : observedState tg₁ = observedState tg₂) :
    observedLabels tg₁ = observedLabels tg₂ := by
  calc
    observedLabels tg₁
        = labelsOfState (observedState tg₁) := by
            simpa using observedLabels_factors_through_state tg₁
    _   = labelsOfState (observedState tg₂) := by
            simp [h]
    _   = observedLabels tg₂ := by
            simpa using (observedLabels_factors_through_state tg₂).symm

theorem observedRegime_eq_of_state_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : observedState tg₁ = observedState tg₂) :
    observedRegime tg₁ = observedRegime tg₂ := by
  calc
    observedRegime tg₁
        = regimeOfState (observedState tg₁) := by
            simpa using observedRegime_factors_through_state tg₁
    _   = regimeOfState (observedState tg₂) := by
            simp [h]
    _   = observedRegime tg₂ := by
            simpa using (observedRegime_factors_through_state tg₂).symm

/--
R4 snapshot reconstructed from:
- `state` as label-side core
- `rowProfile` as geometry-side core
- family as a quotient of `rowProfile`
-/
theorem observedSnapshot_eq_reconstructed_from_state_and_rowProfile
    (tg : ObservedTarget) :
    observedSnapshot tg =
      { labels := labelsOfState (observedState tg)
        regime := regimeOfState (observedState tg)
        geometry := { rowProfile := observedRowProfile tg }
        shapeFamily := shapeFamilyOfProfile (observedRowProfile tg) } := by
  unfold observedSnapshot observedGeometry
  rw [observedLabels_factors_through_state tg]
  rw [observedRegime_factors_through_state tg]
  rw [observedShapeFamily_factors_through_rowProfile tg]
/--
Final catalog-level compression theorem for current audited R4:
snapshot equality is determined by equality of
- `state`
- `rowProfile`
-/
theorem observedSnapshot_eq_of_state_eq_and_rowProfile_eq
    {tg₁ tg₂ : ObservedTarget}
    (hs : observedState tg₁ = observedState tg₂)
    (hp : observedRowProfile tg₁ = observedRowProfile tg₂) :
    observedSnapshot tg₁ = observedSnapshot tg₂ := by
  calc
    observedSnapshot tg₁
        =
          { labels := labelsOfState (observedState tg₁)
            regime := regimeOfState (observedState tg₁)
            geometry := { rowProfile := observedRowProfile tg₁ }
            shapeFamily := shapeFamilyOfProfile (observedRowProfile tg₁) } := by
              simpa using
                observedSnapshot_eq_reconstructed_from_state_and_rowProfile tg₁
    _   =
          { labels := labelsOfState (observedState tg₂)
            regime := regimeOfState (observedState tg₂)
            geometry := { rowProfile := observedRowProfile tg₂ }
            shapeFamily := shapeFamilyOfProfile (observedRowProfile tg₂) } := by
              simp [hs, hp]
    _   = observedSnapshot tg₂ := by
            simpa using
              (observedSnapshot_eq_reconstructed_from_state_and_rowProfile tg₂).symm


theorem observedRegime_not_injective :
    ∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedRegime tg₁ = observedRegime tg₂ := by
  refine ⟨.nfXASqRightPred, .nfXADecorRightPred, ?_, ?_⟩
  · decide
  · rfl

theorem same_regime_different_kernel :
    observedRegime .nfXASqRightPred =
      observedRegime .nfXADecorRightPred
    ∧
    observedKernel .nfXASqRightPred ≠
      observedKernel .nfXADecorRightPred := by
  native_decide

theorem regime_does_not_determine_kernel :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedRegime tg₁ = observedRegime tg₂ ∧
      observedKernel tg₁ ≠ observedKernel tg₂ := by
  refine ⟨.nfXASqRightPred, .nfXADecorRightPred, ?_, ?_⟩
  · rfl
  · decide

theorem same_regime_different_shell :
    observedRegime .nfXASqRightPred =
      observedRegime .nfUSqLiftRightSPred
    ∧
    observedShell .nfXASqRightPred ≠
      observedShell .nfUSqLiftRightSPred := by
  native_decide

theorem regime_does_not_determine_shell :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedRegime tg₁ = observedRegime tg₂ ∧
      observedShell tg₁ ≠ observedShell tg₂ := by
  refine ⟨.nfXASqRightPred, .nfUSqLiftRightSPred, ?_, ?_⟩
  · rfl
  · decide

theorem same_regime_different_state :
    observedRegime .nfXASqRightPred =
      observedRegime .nfUSqLiftRightSPred
    ∧
    observedState .nfXASqRightPred ≠
      observedState .nfUSqLiftRightSPred := by
  native_decide

theorem regime_does_not_determine_state :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedRegime tg₁ = observedRegime tg₂ ∧
      observedState tg₁ ≠ observedState tg₂ := by
  refine ⟨.nfXASqRightPred, .nfUSqLiftRightSPred, ?_, ?_⟩
  · rfl
  · decide

theorem same_regime_different_labels :
    observedRegime .nfXASqRightPred =
      observedRegime .nfUSqLiftRightSPred
    ∧
    observedLabels .nfXASqRightPred ≠
      observedLabels .nfUSqLiftRightSPred := by
  native_decide

theorem regime_does_not_determine_labels :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedRegime tg₁ = observedRegime tg₂ ∧
      observedLabels tg₁ ≠ observedLabels tg₂ := by
  refine ⟨.nfXASqRightPred, .nfUSqLiftRightSPred, ?_, ?_⟩
  · rfl
  · decide

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
