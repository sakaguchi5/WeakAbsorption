import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Patterns

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

inductive SelfEmbeddingShape where
  | rightNest
  | midNest
  | leftNest
  deriving DecidableEq, Repr

def SelfEmbeddingEq {α : Type} :
    SelfEmbeddingShape → Term α → Term α → Term α → Prop
  | .rightNest, u, a, b => u = a.op (b.op u)
  | .midNest,   u, a, b => u = a.op (u.op b)
  | .leftNest,  u, a, b => u = (a.op u).op b

def squareTerm {α : Type} (L : Term α) : Term α :=
  L.op L

structure WeakSquareAdmissible {α : Type} (L : Term α) : Prop where
  root_rigid :
    ∀ {t u : Term α}, t.op u = squareTerm L → t = L ∧ u = L
  no_sqAbsorb :
    NoRootInstance sqAbsorbPat (squareTerm L)
  no_sqStable :
    NoRootInstance sqStablePat (squareTerm L)
  no_decor :
    NoRootInstance decorPat (squareTerm L)
  no_c2c1 :
    NoRootInstance c2c1Pat (squareTerm L)

/-
Medium square-admissibility carries witness data: the obstruction profile.
So it must live in `Type`, not `Prop`.
-/
structure MediumSquareAdmissible {α : Type} (L : Term α) where
  toWeak : WeakSquareAdmissible L
  sqAbsorb_shape : SelfEmbeddingShape
  sqStable_shape : SelfEmbeddingShape
  decor_shape    : SelfEmbeddingShape
  c2c1_shape     : SelfEmbeddingShape

def IsMediumSquareAdmissible {α : Type} (L : Term α) : Prop :=
  Nonempty (MediumSquareAdmissible L)

theorem WeakSquareAdmissible.root_decomposition_iff {α : Type}
    {L t u : Term α} (h : WeakSquareAdmissible L) :
    t.op u = squareTerm L ↔ t = L ∧ u = L := by
  constructor
  · intro hEq
    exact h.root_rigid hEq
  · rintro ⟨rfl, rfl⟩
    rfl

theorem WeakSquareAdmissible.children_equal {α : Type}
    {L t u : Term α} (h : WeakSquareAdmissible L)
    (hEq : t.op u = squareTerm L) :
    t = u := by
  rcases h.root_rigid hEq with ⟨ht, hu⟩
  rw [ht, hu]

def MediumSquareAdmissible.profile {α : Type} {L : Term α}
    (h : MediumSquareAdmissible L) :
    SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape :=
  (h.sqAbsorb_shape, h.sqStable_shape, h.decor_shape, h.c2c1_shape)

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
