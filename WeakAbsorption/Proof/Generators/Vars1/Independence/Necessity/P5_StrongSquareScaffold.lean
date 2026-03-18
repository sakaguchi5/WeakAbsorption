import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.StrongSquareAdmissibility
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_MediumSquareAdmissible

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
Profile-guarded absorbability scaffold for `P5Core`.

This does not yet prove any collapse theorem.
It only records the intended corridor together with the verified medium profile.
-/
def P5Core_absorbabilityCertificate {α : Type} (x p z : Term α) :
    AbsorbabilityCertificate (P5Core x p z) (P5Core_mediumSquareAdmissible x p z) :=
  { corridor := CollapseCorridor.profileGuidedRightLeftRightMid
    guardedProfile := rightLeftRightMidProfileTuple
    profile_ok := by
      simpa [rightLeftRightMidProfileTuple] using P5Core_medium_profile x p z }

/--
Strong square-admissibility scaffold for `P5Core`.

At this stage this is a scaffold object:
medium square-admissibility + chosen absorbability corridor.
-/
def P5Core_strongSquareAdmissible {α : Type} (x p z : Term α) :
    StrongSquareAdmissible (P5Core x p z) :=
  { toMedium := P5Core_mediumSquareAdmissible x p z
    absorbability := P5Core_absorbabilityCertificate x p z }

theorem P5Core_isStrongSquareAdmissible {α : Type} (x p z : Term α) :
    IsStrongSquareAdmissible (P5Core x p z) := by
  exact ⟨P5Core_strongSquareAdmissible x p z⟩

theorem P5Core_strong_profile {α : Type} (x p z : Term α) :
    (P5Core_strongSquareAdmissible (x := x) (p := p) (z := z)).profile =
      rightLeftRightMidProfileTuple := by
  exact (P5Core_strongSquareAdmissible (x := x) (p := p) (z := z)).profile_matches_guard

theorem P5Core_strong_corridor {α : Type} (x p z : Term α) :
    (P5Core_strongSquareAdmissible (x := x) (p := p) (z := z)).corridor =
      CollapseCorridor.profileGuidedRightLeftRightMid := by
  rfl

theorem P5Core_strong_toWeak {α : Type} (x p z : Term α) :
    WeakSquareAdmissible (P5Core x p z) :=
  (P5Core_strongSquareAdmissible x p z).toWeak

theorem P5Core_strong_root_rigid {α : Type} (x p z : Term α) :
    ∀ {t u : Term α},
      t.op u = squareTerm (P5Core x p z) →
      t = P5Core x p z ∧ u = P5Core x p z := by
  exact strongSquareAdmissible_root_rigid (P5Core_strongSquareAdmissible x p z)

theorem P5Core_strong_notPrimitiveRootFamilies {α : Type} (x p z : Term α) :
    NoRootInstance sqAbsorbPat (squareTerm (P5Core x p z)) ∧
    NoRootInstance sqStablePat (squareTerm (P5Core x p z)) ∧
    NoRootInstance decorPat (squareTerm (P5Core x p z)) ∧
    NoRootInstance c2c1Pat (squareTerm (P5Core x p z)) := by
  exact strongSquareAdmissible_notPrimitiveRootFamilies
    (P5Core_strongSquareAdmissible x p z)

theorem P5Term_hasStrongSquareScaffold {α : Type} (x p z : Term α) :
    squareTerm (P5Core x p z) = P5Term x p z ∧
    IsStrongSquareAdmissible (P5Core x p z) := by
  refine ⟨P5Core_squareTerm_eq_P5Term x p z, P5Core_isStrongSquareAdmissible x p z⟩

theorem P5Core_strong_corridor_supports_profile {α : Type} (x p z : Term α) :
    CollapseCorridor.supportsRightLeftRightMid
      (P5Core_strongSquareAdmissible (x := x) (p := p) (z := z)).corridor := by
  simpa [P5Core_strong_corridor x p z] using profileGuidedRightLeftRightMid_supported

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
