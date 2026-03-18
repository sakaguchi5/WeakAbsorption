import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareNotPrimitive

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
The named obstruction-profile class
(right, left, right, mid).
-/
def RightLeftRightMidProfile {α : Type} (B : MediumSquareBoundary α) : Prop :=
  B.profile =
    ( SelfEmbeddingShape.rightNest
    , SelfEmbeddingShape.leftNest
    , SelfEmbeddingShape.rightNest
    , SelfEmbeddingShape.midNest )

/-- 4-tuple projections for profile tuples. -/
def fst4 {α β γ δ : Type} (p : α × β × γ × δ) : α :=
  p.1

def snd4 {α β γ δ : Type} (p : α × β × γ × δ) : β :=
  p.2.1

def thd4 {α β γ δ : Type} (p : α × β × γ × δ) : γ :=
  p.2.2.1

def fth4 {α β γ δ : Type} (p : α × β × γ × δ) : δ :=
  p.2.2.2

theorem rightLeftRightMidProfile_sqAbsorb {α : Type} {B : MediumSquareBoundary α}
    (h : RightLeftRightMidProfile B) :
    B.admissible.sqAbsorb_shape = SelfEmbeddingShape.rightNest := by
  have h1 := congrArg fst4 h
  simpa [RightLeftRightMidProfile, MediumSquareBoundary.profile,
    MediumSquareAdmissible.profile, fst4] using h1

theorem rightLeftRightMidProfile_sqStable {α : Type} {B : MediumSquareBoundary α}
    (h : RightLeftRightMidProfile B) :
    B.admissible.sqStable_shape = SelfEmbeddingShape.leftNest := by
  have h2 := congrArg snd4 h
  simpa [RightLeftRightMidProfile, MediumSquareBoundary.profile,
    MediumSquareAdmissible.profile, snd4] using h2

theorem rightLeftRightMidProfile_decor {α : Type} {B : MediumSquareBoundary α}
    (h : RightLeftRightMidProfile B) :
    B.admissible.decor_shape = SelfEmbeddingShape.rightNest := by
  have h3 := congrArg thd4 h
  simpa [RightLeftRightMidProfile, MediumSquareBoundary.profile,
    MediumSquareAdmissible.profile, thd4] using h3

theorem rightLeftRightMidProfile_c2c1 {α : Type} {B : MediumSquareBoundary α}
    (h : RightLeftRightMidProfile B) :
    B.admissible.c2c1_shape = SelfEmbeddingShape.midNest := by
  have h4 := congrArg fth4 h
  simpa [RightLeftRightMidProfile, MediumSquareBoundary.profile,
    MediumSquareAdmissible.profile, fth4] using h4

/--
Any boundary object in the named profile class has:
- a canonical square core,
- rigid root decomposition,
- exclusion from primitive R4 root seeds,
- the named profile components.
-/
theorem rightLeftRightMidProfile_summary {α : Type} {B : MediumSquareBoundary α}
    (hProf : RightLeftRightMidProfile B) :
    (∃ L : Term α, squareTerm L = B.term ∧
        ∀ {t u : Term α}, t.op u = B.term ↔ t = L ∧ u = L) ∧
    ¬ IsPrimitiveR4RootSeed B.term ∧
    B.admissible.sqAbsorb_shape = SelfEmbeddingShape.rightNest ∧
    B.admissible.sqStable_shape = SelfEmbeddingShape.leftNest ∧
    B.admissible.decor_shape = SelfEmbeddingShape.rightNest ∧
    B.admissible.c2c1_shape = SelfEmbeddingShape.midNest := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨B.core, rfl, ?_⟩
    intro t u
    exact B.root_decomposition_iff
  · exact mediumSquareBoundary_not_primitiveR4RootSeed (show IsMediumSquareBoundary B.term from ⟨B, rfl⟩)
  · exact rightLeftRightMidProfile_sqAbsorb hProf
  · exact rightLeftRightMidProfile_sqStable hProf
  · exact rightLeftRightMidProfile_decor hProf
  · exact rightLeftRightMidProfile_c2c1 hProf

/--
Any term represented by a boundary object in the named profile class is a
square outsider to the current primitive R4 root-seed class.
-/
theorem rightLeftRightMidProfile_square_outsider {α : Type} {T : Term α}
    (h : ∃ B : MediumSquareBoundary α, RightLeftRightMidProfile B ∧ B.term = T) :
    (∃ L : Term α, squareTerm L = T) ∧ ¬ IsPrimitiveR4RootSeed T := by
  rcases h with ⟨B, hProf, hT⟩
  rcases rightLeftRightMidProfile_summary hProf with
    ⟨hCore, hNot, hSA, hSS, hD, hC⟩
  refine ⟨?_, ?_⟩
  · rcases hCore with ⟨L, hSq, hRigid⟩
    exact ⟨L, by simpa [hT] using hSq⟩
  · simpa [hT] using hNot

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
