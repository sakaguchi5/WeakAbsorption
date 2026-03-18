import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.RightLeftRightMidTermClass

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/-!
This file separates three levels of uniqueness facts.

1. Core rigidity for `MediumSquareBoundary` objects with the same represented term.
2. Pure structural injectivity of `squareTerm`.
3. Right/left/right/mid consequences built on top of the previous two layers.

The final theorem `rightLeftRightMidTerm_witness_core_unique` is intentionally
kept as a thin packaging lemma for chosen witnesses. Its mathematical content
comes entirely from `mediumSquareBoundary_core_unique_of_same_term`; the final
`simp` only unwraps the chosen witnesses.
-/

/--
Core rigidity for medium square boundary objects:
if two boundary objects represent the same term, then their cores agree.
This is the main uniqueness theorem in this file.
-/
theorem mediumSquareBoundary_core_unique_of_same_term {α : Type}
    {B₁ B₂ : MediumSquareBoundary α}
    (h : B₁.term = B₂.term) :
    B₁.core = B₂.core := by
  have h1 : B₁.core.op B₁.core = B₂.term := by
    simpa [MediumSquareBoundary.term] using h
  have h2 : B₁.core = B₂.core ∧ B₁.core = B₂.core := by
    exact B₂.root_rigid h1
  exact h2.1

/--
A direct corollary of core rigidity at the level of square terms.
-/
theorem mediumSquareBoundary_square_core_unique_of_same_term {α : Type}
    {B₁ B₂ : MediumSquareBoundary α}
    (h : B₁.term = B₂.term) :
    squareTerm B₁.core = squareTerm B₂.core := by
  have hcore : B₁.core = B₂.core :=
    mediumSquareBoundary_core_unique_of_same_term h
  rw [hcore]

/--
Pure structural injectivity of `squareTerm`.
This theorem does not use any profile or boundary hypotheses.
-/
theorem squareTerm_injective {α : Type} :
    ∀ {L₁ L₂ : Term α}, squareTerm L₁ = squareTerm L₂ → L₁ = L₂ := by
  intro L₁ L₂ hEq
  injection hEq

/--
If a term is given as `squareTerm L` in two ways, then the square core is unique.
This is the target-shaped form of `squareTerm_injective`.
-/
theorem mediumSquareBoundary_term_has_unique_core {α : Type} {T : Term α} :
    ∀ {L₁ L₂ : Term α},
      squareTerm L₁ = T →
      squareTerm L₂ = T →
      L₁ = L₂ := by
  intro L₁ L₂ h₁ h₂
  exact squareTerm_injective (h₁.trans h₂.symm)

/--
For a right/left/right/mid term, the extracted square core is unique.
This is a genuine profile-side consequence, obtained from
`rightLeftRightMidTerm_unique_root_core`.
-/
theorem rightLeftRightMidTerm_core_unique {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    ∀ {L₁ L₂ : Term α},
      squareTerm L₁ = T →
      squareTerm L₂ = T →
      L₁ = L₂ := by
  intro L₁ L₂ h₁ h₂
  rcases rightLeftRightMidTerm_unique_root_core h with ⟨L, hSq, hRigid⟩
  have hL₁ : L₁ = L := by
    exact (hRigid.mp h₁).1
  have hL₂ : L₂ = L := by
    exact (hRigid.mp h₂).1
  rw [hL₁, hL₂]

/--
Packaging lemma for chosen right/left/right/mid witnesses.

This theorem is not a new source of rigidity. Its mathematical content is exactly
the reduction to `mediumSquareBoundary_core_unique_of_same_term` after showing
that the two chosen witnesses represent the same term. The final `simp` only
unfolds the chosen witnesses.
-/
theorem rightLeftRightMidTerm_witness_core_unique {α : Type} {T : Term α}
    (h₁ : ∃ B₁ : MediumSquareBoundary α, RightLeftRightMidProfile B₁ ∧ B₁.term = T)
    (h₂ : ∃ B₂ : MediumSquareBoundary α, RightLeftRightMidProfile B₂ ∧ B₂.term = T) :
    let B₁ := Classical.choose h₁
    let B₂ := Classical.choose h₂
    B₁.core = B₂.core := by
  classical
  let B₁ : MediumSquareBoundary α := Classical.choose h₁
  let B₂ : MediumSquareBoundary α := Classical.choose h₂
  have hT₁ : B₁.term = T := by
    simpa [B₁] using (Classical.choose_spec h₁).2
  have hT₂ : B₂.term = T := by
    simpa [B₂] using (Classical.choose_spec h₂).2
  have hsame : B₁.term = B₂.term := by
    exact hT₁.trans hT₂.symm
  simp [B₁, B₂, mediumSquareBoundary_core_unique_of_same_term hsame]

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
