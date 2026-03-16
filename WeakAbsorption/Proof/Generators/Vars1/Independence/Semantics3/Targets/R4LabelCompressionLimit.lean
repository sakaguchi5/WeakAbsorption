import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4CompressedSnapshotAudit

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
A simpler label-side object than `ObservedTargetLabels`:
the pair `(kernel, shell)`.
-/
def observedKernelShell (tg : ObservedTarget) :
    ObservedKernelClass × ObservedShellKind :=
  (observedKernel tg, observedShell tg)

/--
Current audited R4 state is already injective on targets.

Interpretation:
- `state` is currently too fine to count as a genuine compression.
-/
theorem observedState_injective :
    Function.Injective observedState := by
  intro tg₁ tg₂ h
  cases tg₁ <;> cases tg₂ <;>
    simp [observedState] at h ⊢

/--
Current audited R4 target equality can be read off from state alone.
-/
theorem observedState_eq_implies_target_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : observedState tg₁ = observedState tg₂) :
    tg₁ = tg₂ := by
  exact observedState_injective h

/--
Kernel alone is not enough to determine the target.
-/
theorem observedKernel_not_injective :
    ∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedKernel tg₁ = observedKernel tg₂ := by
  refine ⟨.nfXASqRightPred, .nfUSqLiftRightSPred, ?_, ?_⟩
  · decide
  · rfl

/--
Shell alone is not enough to determine the target.
-/
theorem observedShell_not_injective :
    ∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedShell tg₁ = observedShell tg₂ := by
  refine ⟨.nfXASqRightPred, .nfXADecorRightPred, ?_, ?_⟩
  · decide
  · rfl


theorem kernel_eq_and_shell_eq_implies_target_eq
    {tg₁ tg₂ : ObservedTarget}
    (hk : observedKernel tg₁ = observedKernel tg₂)
    (hs : observedShell tg₁ = observedShell tg₂) :
    tg₁ = tg₂ := by
  cases tg₁ <;> cases tg₂ <;>
    simp [observedKernel, observedShell] at hk hs ⊢

theorem observedKernelShell_injective :
    Function.Injective observedKernelShell := by
  intro tg₁ tg₂ h
  exact kernel_eq_and_shell_eq_implies_target_eq
    (congrArg Prod.fst h)
    (congrArg Prod.snd h)



/--
Current audited R4 target equality can be read off from `(kernel, shell)`.
-/
theorem observedKernelShell_eq_implies_target_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : observedKernelShell tg₁ = observedKernelShell tg₂) :
    tg₁ = tg₂ := by
  exact observedKernelShell_injective h

/--
`state` factors through `(kernel, shell)` on the current audited R4 catalog.
-/
def stateOfKernelShell :
    ObservedKernelClass → ObservedShellKind → Option ObservedState
  | .saKernel,         .rightShell       => some .saRight
  | .saKernel,         .leftLift         => some .saLeftLift
  | .decorRightKernel, .rightShell       => some .decorRight_right
  | .decorRightKernel, .leftLift         => some .decorRight_leftLift
  | .decorLeftKernel,  .rightShell       => some .decorLeft_right
  | .decorLeftKernel,  .leftLift         => some .decorLeft_leftLift
  | .stableKernel,     .leftLift         => some .stable_leftLift
  | .holeKernel,       .rootShell        => some .hole_root
  | .decorHoleKernel,  .rootShell        => some .decorHole_root
  | .aaKernel,         .rightShell       => some .aa_right
  | .aaKernel,         .leftLift         => some .aa_leftLift
  | .bridgeKernel,     .bridgeSplitShell => some .bridge_split
  | _, _                                  => none

theorem observedState_factors_through_kernelShell
    (tg : ObservedTarget) :
    stateOfKernelShell (observedKernel tg) (observedShell tg) =
      some (observedState tg) := by
  cases tg <;> rfl

/--
Conceptual summary:
on the current audited R4 catalog,
- `kernel` alone does not determine the target
- `shell` alone does not determine the target
- `state` does determine the target
- `(kernel, shell)` also determines the target

So the label-side sector has not yet been genuinzely compressed.
-/
theorem label_side_not_yet_genuinely_compressed :
    (∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedKernel tg₁ = observedKernel tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      tg₁ ≠ tg₂ ∧ observedShell tg₁ = observedShell tg₂)
    ∧
    Function.Injective observedState
    ∧
    Function.Injective observedKernelShell := by
  refine ⟨observedKernel_not_injective, observedShell_not_injective,
    observedState_injective, observedKernelShell_injective⟩



theorem observedState_eq_iff_kernelShell_eq
    {tg₁ tg₂ : ObservedTarget} :
    observedState tg₁ = observedState tg₂ ↔
      (observedKernel tg₁ = observedKernel tg₂ ∧
       observedShell tg₁ = observedShell tg₂) := by
  constructor
  · intro hs
    constructor
    · calc
        observedKernel tg₁
            = kernelOfState (observedState tg₁) := by
                simpa using observedKernel_factors_through_state tg₁
        _   = kernelOfState (observedState tg₂) := by
                simp [hs]
        _   = observedKernel tg₂ := by
                simpa using (observedKernel_factors_through_state tg₂).symm
    · calc
        observedShell tg₁
            = shellOfState (observedState tg₁) := by
                simpa using observedShell_factors_through_state tg₁
        _   = shellOfState (observedState tg₂) := by
                simp [hs]
        _   = observedShell tg₂ := by
                simpa using (observedShell_factors_through_state tg₂).symm
  · rintro ⟨hk, hs⟩
    have ht : tg₁ = tg₂ := kernel_eq_and_shell_eq_implies_target_eq hk hs
    simp [ht]

theorem same_kernel_and_regime_different_target :
    observedKernel .nfXASqRightPred =
      observedKernel .nfUSqLiftRightSPred
    ∧
    observedRegime .nfXASqRightPred =
      observedRegime .nfUSqLiftRightSPred
    ∧
    (.nfXASqRightPred : ObservedTarget) ≠ .nfUSqLiftRightSPred := by
  decide

theorem kernel_and_regime_do_not_determine_target :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedKernel tg₁ = observedKernel tg₂ ∧
      observedRegime tg₁ = observedRegime tg₂ ∧
      tg₁ ≠ tg₂ := by
  refine ⟨.nfXASqRightPred, .nfUSqLiftRightSPred, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide

theorem same_shell_and_regime_different_target :
    observedShell .nfXASqRightPred =
      observedShell .nfXADecorRightPred
    ∧
    observedRegime .nfXASqRightPred =
      observedRegime .nfXADecorRightPred
    ∧
    (.nfXASqRightPred : ObservedTarget) ≠ .nfXADecorRightPred := by
  decide

theorem shell_and_regime_do_not_determine_target :
    ∃ tg₁ tg₂ : ObservedTarget,
      observedShell tg₁ = observedShell tg₂ ∧
      observedRegime tg₁ = observedRegime tg₂ ∧
      tg₁ ≠ tg₂ := by
  refine ⟨.nfXASqRightPred, .nfXADecorRightPred, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide

theorem regime_is_strict_quotient_of_labels :
    (∀ tg : ObservedTarget,
      observedRegime tg = regimeOfLabels (observedLabels tg))
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
      observedRegime tg₁ = observedRegime tg₂ ∧
      observedLabels tg₁ ≠ observedLabels tg₂) := by
  constructor
  · intro tg
    exact observedRegime_factors_through_labels tg
  · exact regime_does_not_determine_labels

theorem label_side_current_picture :
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
    Function.Injective observedState := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact observedKernel_not_injective
  · exact observedShell_not_injective
  · exact observedRegime_not_injective
  · exact observedKernelShell_injective
  · exact observedState_injective

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
