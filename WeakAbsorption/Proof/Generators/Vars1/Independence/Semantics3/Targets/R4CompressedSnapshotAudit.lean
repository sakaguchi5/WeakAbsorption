import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4CompressedSnapshot

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
If two targets have the same compressed snapshot, then their observed snapshots agree.

This is the conceptual meaning of the reconstruction theorem:
on the current audited R4 catalog, `R4CompressedSnapshot` is sufficient
to recover the full observed snapshot.
-/
theorem compressedSnapshot_eq_implies_observedSnapshot_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : compressedSnapshot tg₁ = compressedSnapshot tg₂) :
    observedSnapshot tg₁ = observedSnapshot tg₂ := by
  calc
    observedSnapshot tg₁
        = reconstruct (compressedSnapshot tg₁) := by
            symm
            exact reconstruct_compressedSnapshot tg₁
    _   = reconstruct (compressedSnapshot tg₂) := by
            simp [h]
    _   = observedSnapshot tg₂ := by
            exact reconstruct_compressedSnapshot tg₂

/--
Catalog-level injectivity of `compressedSnapshot`.

This says that, on the current audited R4 target universe,
the compressed image still separates targets.
-/
theorem compressedSnapshot_injective :
    Function.Injective compressedSnapshot := by
  intro tg₁ tg₂ h
  have hs : observedState tg₁ = observedState tg₂ := by
    simpa [compressedSnapshot] using congrArg R4CompressedSnapshot.state h
  have hp : observedRowProfile tg₁ = observedRowProfile tg₂ := by
    simpa [compressedSnapshot] using congrArg R4CompressedSnapshot.rowProfile h
  cases tg₁ <;> cases tg₂ <;>
    simp [observedState, observedRowProfile] at hs hp ⊢

/--
Equivalent explicit form:
same compressed snapshot implies same target.
-/
theorem compressedSnapshot_eq_implies_target_eq
    {tg₁ tg₂ : ObservedTarget}
    (h : compressedSnapshot tg₁ = compressedSnapshot tg₂) :
    tg₁ = tg₂ := by
  exact compressedSnapshot_injective h

/--
As a corollary, the observed snapshot map is also injective on the
current audited R4 target universe.
-/
theorem observedSnapshot_injective :
    Function.Injective observedSnapshot := by
  intro tg₁ tg₂ h
  apply compressedSnapshot_injective
  calc
    compressedSnapshot tg₁ = compress (observedSnapshot tg₁) := by
      symm
      exact compress_observedSnapshot tg₁
    _ = compress (observedSnapshot tg₂) := by
      simp [h]
    _ = compressedSnapshot tg₂ := by
      exact compress_observedSnapshot tg₂

/--
Current audited R4 target equality can be read off from the pair
`(state, rowProfile)`.
-/
theorem state_and_rowProfile_determine_target
    {tg₁ tg₂ : ObservedTarget}
    (hs : observedState tg₁ = observedState tg₂)
    (hp : observedRowProfile tg₁ = observedRowProfile tg₂) :
    tg₁ = tg₂ := by
  apply compressedSnapshot_injective
  cases tg₁ <;> cases tg₂ <;>
    simp [compressedSnapshot, observedState, observedRowProfile] at hs hp ⊢

/--
Current audited R4 target equality can also be read off from the full
sector-core pair `(labels, geometry)`.
-/
theorem labels_and_geometry_determine_target
    {tg₁ tg₂ : ObservedTarget}
    (hl : observedLabels tg₁ = observedLabels tg₂)
    (hg : observedGeometry tg₁ = observedGeometry tg₂) :
    tg₁ = tg₂ := by
  have hs : observedState tg₁ = observedState tg₂ := by
    simpa [observedLabels] using congrArg ObservedTargetLabels.state hl
  have hp : observedRowProfile tg₁ = observedRowProfile tg₂ := by
    simpa [observedGeometry] using congrArg ObservedRowGeometry.rowProfile hg
  exact state_and_rowProfile_determine_target hs hp

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
