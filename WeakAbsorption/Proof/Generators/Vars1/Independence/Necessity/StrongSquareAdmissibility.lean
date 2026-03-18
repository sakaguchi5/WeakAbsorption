import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.SquareAdmissibility

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

abbrev ObstructionProfile :=
  SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape

def rightLeftRightMidProfileTuple : ObstructionProfile :=
  ( SelfEmbeddingShape.rightNest
  , SelfEmbeddingShape.leftNest
  , SelfEmbeddingShape.rightNest
  , SelfEmbeddingShape.midNest )

/--
Named collapse corridors for future strong square-admissibility work.

At this stage these are only tags for the intended absorption route.
They are not yet proofs of absorbability.
-/
inductive CollapseCorridor where
  | doubleSqLike
  | towerLike
  | profileGuidedRightLeftRightMid
  | other
  deriving DecidableEq, Repr

/--
An absorbability certificate is, for now, a profile-guarded corridor choice.

This is deliberately a scaffold:
it records which obstruction profile the medium core has,
and which collapse corridor is intended for it.
-/
structure AbsorbabilityCertificate {α : Type} (L : Term α)
    (h : MediumSquareAdmissible L) where
  corridor : CollapseCorridor
  guardedProfile : ObstructionProfile
  profile_ok : h.profile = guardedProfile

/--
Strong square-admissibility is defined as:

- a medium square-admissibility witness,
- together with an absorbability certificate.

At this stage, the absorbability certificate is still scaffolding data,
not yet a proved collapse theorem.
-/
structure StrongSquareAdmissible {α : Type} (L : Term α) where
  toMedium : MediumSquareAdmissible L
  absorbability : AbsorbabilityCertificate L toMedium

def IsStrongSquareAdmissible {α : Type} (L : Term α) : Prop :=
  Nonempty (StrongSquareAdmissible L)

def StrongSquareAdmissible.profile {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) : ObstructionProfile :=
  h.toMedium.profile

def StrongSquareAdmissible.corridor {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) : CollapseCorridor :=
  h.absorbability.corridor

def StrongSquareAdmissible.guardedProfile {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) : ObstructionProfile :=
  h.absorbability.guardedProfile

theorem StrongSquareAdmissible.profile_matches_guard {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) :
    h.profile = h.guardedProfile := by
  exact h.absorbability.profile_ok

theorem StrongSquareAdmissible.toWeak {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) :
    WeakSquareAdmissible L :=
  h.toMedium.toWeak

theorem strongSquareAdmissible_isMedium {α : Type} {L : Term α}
    (h : IsStrongSquareAdmissible L) :
    IsMediumSquareAdmissible L := by
  rcases h with ⟨hS⟩
  exact ⟨hS.toMedium⟩

theorem strongSquareAdmissible_root_rigid {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) :
    ∀ {t u : Term α}, t.op u = squareTerm L → t = L ∧ u = L := by
  exact h.toWeak.root_rigid

theorem strongSquareAdmissible_notPrimitiveRootFamilies {α : Type} {L : Term α}
    (h : StrongSquareAdmissible L) :
    NoRootInstance sqAbsorbPat (squareTerm L) ∧
    NoRootInstance sqStablePat (squareTerm L) ∧
    NoRootInstance decorPat (squareTerm L) ∧
    NoRootInstance c2c1Pat (squareTerm L) := by
  refine ⟨h.toWeak.no_sqAbsorb, h.toWeak.no_sqStable, h.toWeak.no_decor, h.toWeak.no_c2c1⟩

def CollapseCorridor.supportsRightLeftRightMid : CollapseCorridor → Prop
  | .doubleSqLike => True
  | .towerLike => True
  | .profileGuidedRightLeftRightMid => True
  | .other => False

theorem profileGuidedRightLeftRightMid_supported :
    CollapseCorridor.supportsRightLeftRightMid
      CollapseCorridor.profileGuidedRightLeftRightMid := by
  trivial

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
