import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4StateLabelCompression
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowCoordinates
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Mechanisms

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity
open Necessity.ProofCore

/--
Forget the legacy presentation vocabulary down to the Semantics3 coarse rule-kind.
-/
def atomToRuleKind : RowSlot → ObservedRuleKind
  | .sqAbsorb => .sqAbsorb
  | .sqStable => .sqStable
  | .decor    => .decor
  | .c2c1     => .c2c1

/--
Forget the legacy channel vocabulary down to the Semantics3 coarse side.
-/
def atomToSide : CtxChannel → ObservedSide
  | .root  => .root
  | .left  => .left
  | .right => .right

/--
Forget one exact atom to one Semantics3 coarse coordinate.
This intentionally throws away the legacy `tag` component.
-/
def atomToShapeCoord (a : RowAtom) : ObservedShapeCoord :=
  { kind := atomToRuleKind a.slot
    side := atomToSide a.channel }

/--
Fixed coordinate order used to turn exact atoms into a Semantics3 row-profile.

The order is chosen so that the resulting profile matches the current
`observedRowProfile` conventions already used in `R4SnapshotData`.
-/
def observedShapeCoordBasis : List ObservedShapeCoord :=
  [ { kind := .sqAbsorb, side := .right }
  , { kind := .sqAbsorb, side := .left }
  , { kind := .sqAbsorb, side := .root }
  , { kind := .sqStable, side := .left }
  , { kind := .decor,    side := .right }
  , { kind := .decor,    side := .left }
  , { kind := .decor,    side := .root }
  , { kind := .c2c1,     side := .root }
  ]

/-- Count how many exact atoms map to one coarse coordinate. -/
def countAtomsAtCoord (atoms : List RowAtom) (c : ObservedShapeCoord) : Nat :=
  (atoms.filter (fun a => atomToShapeCoord a = c)).length

/--
Forget an exact-row atom list to the Semantics3 multiplicity-aware row profile.
-/
def rowProfileOfAtoms (atoms : List RowAtom) : ObservedRowProfile :=
  ObservedRowProfile.ofCounts <|
    ((observedShapeCoordBasis.map (fun c => (c, countAtomsAtCoord atoms c))).filter
      (fun e => e.snd ≠ 0))

/--
For the current audited R4 targets, forgetting exact atoms recovers the Semantics3 row profile.
-/
theorem rowProfileOfTargetAtoms_eq_observedRowProfile
    (tg : ObservedTarget) :
    rowProfileOfAtoms (rowAtomsOfTarget tg) = observedRowProfile tg := by
  cases tg <;> decide

/--
State-level version of the same forgetful-factorization fact.
-/
theorem rowProfileOfStateAtoms_eq_observedRowProfile
    (σ : ObservedState) :
    rowProfileOfAtoms (rowAtomsOfState σ) =
      observedRowProfile (stateTarget σ) := by
  cases σ <;> decide

/--
The forgetful map is not injective: distinct exact atoms may collapse
to the same coarse coordinate once the legacy `tag` is forgotten.
-/
theorem atomToShapeCoord_forgets_tag :
    let a₁ : RowAtom :=
      { slot := .sqAbsorb, channel := .right, tag := .nfXA }
    let a₂ : RowAtom :=
      { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred }
    a₁ ≠ a₂ ∧ atomToShapeCoord a₁ = atomToShapeCoord a₂ := by
  decide

/--
Current audited R4 shows that row-profile does not determine the label sector:
same row-profile, different labels.
-/
theorem same_rowProfile_different_labels :
    observedRowProfile .nfXADecorRightPred =
      observedRowProfile .nfXADecorLeftPred
    ∧
    observedLabels .nfXADecorRightPred ≠
      observedLabels .nfXADecorLeftPred := by
  decide

/--
Current audited R4 shows that row-profile does not determine the state either:
same row-profile, different states.
-/
theorem same_rowProfile_different_state :
    observedRowProfile .nfXADecorRightPred =
      observedRowProfile .nfXADecorLeftPred
    ∧
    observedState .nfXADecorRightPred ≠
      observedState .nfXADecorLeftPred := by
  decide

/--
Conceptual summary theorem:
- exact atoms forget to rowProfile
- the forgetful map is non-injective
- rowProfile is therefore a quotient of exact-row data, not a faithful encoding
-/
theorem rowProfile_is_a_genuine_quotient :
    (∀ tg : ObservedTarget,
      rowProfileOfAtoms (rowAtomsOfTarget tg) = observedRowProfile tg)
    ∧
    (∃ a₁ a₂ : RowAtom,
      a₁ ≠ a₂ ∧ atomToShapeCoord a₁ = atomToShapeCoord a₂) := by
  constructor
  · intro tg
    exact rowProfileOfTargetAtoms_eq_observedRowProfile tg
  · refine ⟨
      { slot := .sqAbsorb, channel := .right, tag := .nfXA },
      { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred },
      ?_, ?_⟩
    · decide
    · rfl

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
