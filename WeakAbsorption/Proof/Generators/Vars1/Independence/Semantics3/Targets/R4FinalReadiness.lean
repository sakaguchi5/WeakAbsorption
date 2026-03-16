import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4CompressionSummary

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Relative minimality audit for the current row-geometry sector.

What this bundles:
- `rowProfile` is sufficient to recover the currently audited row observables.
- the coarser candidates below it fail:
  `rowShape`, `shapeFamily`, `shapeFamily + counts`, and `counts`.
-/
theorem relative_minimality_geometry :
    (∀ {tg₁ tg₂ : ObservedTarget},
        observedRowProfile tg₁ = observedRowProfile tg₂ →
        observedRowShape tg₁ = observedRowShape tg₂ ∧
        observedAtomCount tg₁ = observedAtomCount tg₂ ∧
        observedShapeCount tg₁ = observedShapeCount tg₂ ∧
        observedShapeFamily tg₁ = observedShapeFamily tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedRowShape tg₁ = observedRowShape tg₂ ∧
        observedShapeFamily tg₁ ≠ observedShapeFamily tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedShapeFamily tg₁ = observedShapeFamily tg₂ ∧
        observedRowProfile tg₁ ≠ observedRowProfile tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedShapeFamily tg₁ = observedShapeFamily tg₂ ∧
        observedAtomCount tg₁ = observedAtomCount tg₂ ∧
        observedShapeCount tg₁ = observedShapeCount tg₂ ∧
        observedRowProfile tg₁ ≠ observedRowProfile tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedAtomCount tg₁ = observedAtomCount tg₂ ∧
        observedShapeCount tg₁ = observedShapeCount tg₂ ∧
        observedShapeFamily tg₁ ≠ observedShapeFamily tg₂) := by
  refine ⟨?_, rowShape_does_not_determine_shapeFamily,
    shapeFamily_does_not_determine_rowProfile,
    shapeFamily_and_counts_do_not_determine_rowProfile,
    counts_do_not_determine_shapeFamily⟩
  intro tg₁ tg₂ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      observedRowShape tg₁ = (observedRowProfile tg₁).support := by
        simpa using observedRowShape_factors_through_rowProfile tg₁
      _ = (observedRowProfile tg₂).support := by
        simp [h]
      _ = observedRowShape tg₂ := by
        simpa using (observedRowShape_factors_through_rowProfile tg₂).symm
  · calc
      observedAtomCount tg₁ = (observedRowProfile tg₁).atomCount := by
        simpa using observedAtomCount_factors_through_rowProfile tg₁
      _ = (observedRowProfile tg₂).atomCount := by
        simp [h]
      _ = observedAtomCount tg₂ := by
        simpa using (observedAtomCount_factors_through_rowProfile tg₂).symm
  · calc
      observedShapeCount tg₁ = (observedRowProfile tg₁).shapeCount := by
        simpa using observedShapeCount_factors_through_rowProfile tg₁
      _ = (observedRowProfile tg₂).shapeCount := by
        simp [h]
      _ = observedShapeCount tg₂ := by
        simpa using (observedShapeCount_factors_through_rowProfile tg₂).symm
  · have hgeom :
        (observedGeometry tg₁).rowProfile =
        (observedGeometry tg₂).rowProfile := by
        simpa using h
    exact observedShapeFamily_eq_of_rowProfile_eq hgeom

/--
Relative minimality audit for the current label sector.

Within the currently audited candidate family, only
`observedKernelShell` and `observedState` survive as separating cores.
-/
theorem relative_minimality_label :
    (∃ tg₁ tg₂ : ObservedTarget,
        tg₁ ≠ tg₂ ∧ observedKernel tg₁ = observedKernel tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        tg₁ ≠ tg₂ ∧ observedShell tg₁ = observedShell tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        tg₁ ≠ tg₂ ∧ observedRegime tg₁ = observedRegime tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedKernel tg₁ = observedKernel tg₂ ∧
        observedRegime tg₁ = observedRegime tg₂ ∧
        tg₁ ≠ tg₂)
    ∧
    (∃ tg₁ tg₂ : ObservedTarget,
        observedShell tg₁ = observedShell tg₂ ∧
        observedRegime tg₁ = observedRegime tg₂ ∧
        tg₁ ≠ tg₂)
    ∧
    Function.Injective observedKernelShell
    ∧
    Function.Injective observedState := by
  refine ⟨observedKernel_not_injective,
    observedShell_not_injective,
    observedRegime_not_injective,
    kernel_and_regime_do_not_determine_target,
    shell_and_regime_do_not_determine_target,
    observedKernelShell_injective,
    observedState_injective⟩

/-- The visible `(kernel, shell)` pair induced by a state. -/
def kernelShellOfState (st : ObservedState) :
    ObservedKernelClass × ObservedShellKind :=
  (kernelOfState st, shellOfState st)

theorem kernelShellOfState_observedState (tg : ObservedTarget) :
    kernelShellOfState (observedState tg) = observedKernelShell tg := by
  apply Prod.ext
  · simp [kernelShellOfState, observedKernelShell,
      observedKernel_factors_through_state]
  · simp [kernelShellOfState, observedKernelShell,
      observedShell_factors_through_state]

theorem stateOfKernelShell_kernelShellOfState (st : ObservedState) :
    stateOfKernelShell
        (kernelShellOfState st).1
        (kernelShellOfState st).2
      = some st := by
  cases st <;> rfl

theorem observedState_eq_iff_observedKernelShell_eq
    {tg₁ tg₂ : ObservedTarget} :
    observedState tg₁ = observedState tg₂ ↔
      observedKernelShell tg₁ = observedKernelShell tg₂ := by
  constructor
  · intro hs
    have hks :
        observedKernel tg₁ = observedKernel tg₂ ∧
        observedShell tg₁ = observedShell tg₂ :=
      (observedState_eq_iff_kernelShell_eq (tg₁ := tg₁) (tg₂ := tg₂)).1 hs
    apply Prod.ext
    · exact hks.1
    · exact hks.2
  · intro hks
    exact (observedState_eq_iff_kernelShell_eq (tg₁ := tg₁) (tg₂ := tg₂)).2
      ⟨congrArg Prod.fst hks, congrArg Prod.snd hks⟩

/--
On the current audited image, `state` and `(kernel, shell)` are equivalent
presentations of the same label-side information.
-/
theorem state_kernelShell_equivalence_on_image :
    (∀ tg : ObservedTarget,
        kernelShellOfState (observedState tg) = observedKernelShell tg)
    ∧
    (∀ tg : ObservedTarget,
        stateOfKernelShell (observedKernel tg) (observedShell tg)
          = some (observedState tg))
    ∧
    (∀ {tg₁ tg₂ : ObservedTarget},
        observedState tg₁ = observedState tg₂ ↔
          observedKernelShell tg₁ = observedKernelShell tg₂) := by
  refine ⟨kernelShellOfState_observedState,
    observedState_factors_through_kernelShell,
    ?_⟩
  intro tg₁ tg₂
  exact observedState_eq_iff_observedKernelShell_eq

/--
Reconstruct a current audited snapshot from the candidate primitive
`(kernel, shell, rowProfile)`.

This is partial because not every arbitrary `(kernel, shell)` pair is realizable.
-/
def reconstructFromKernelShellAndRowProfile
    (ks : ObservedKernelClass × ObservedShellKind)
    (rp : ObservedRowProfile) :
    Option ObservedKernelSnapshot :=
  match stateOfKernelShell ks.1 ks.2 with
  | some st =>
      some
        { labels := { kernel := ks.1, shell := ks.2, state := st }
          regime := regimeOfState st
          geometry := { rowProfile := rp }
          shapeFamily := shapeFamilyOfProfile rp }
  | none => none

/--
Target-indexed reconstruction theorem for the preferred primitive candidate
`(kernel, shell, rowProfile)`.
-/
theorem sector_core_reconstruction (tg : ObservedTarget) :
    reconstructFromKernelShellAndRowProfile
        (observedKernelShell tg) (observedRowProfile tg)
      = some (observedSnapshot tg) := by
  cases tg <;> rfl

/--
Separation theorem for the same primitive candidate.
If `(kernel, shell)` and `rowProfile` agree, the target already agrees.
-/
theorem kernelShell_and_rowProfile_determine_target
    {tg₁ tg₂ : ObservedTarget}
    (hks : observedKernelShell tg₁ = observedKernelShell tg₂)
    (hp  : observedRowProfile tg₁ = observedRowProfile tg₂) :
    tg₁ = tg₂ := by
  exact state_and_rowProfile_determine_target
    ((observedState_eq_iff_observedKernelShell_eq (tg₁ := tg₁) (tg₂ := tg₂)).2 hks)
    hp

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
