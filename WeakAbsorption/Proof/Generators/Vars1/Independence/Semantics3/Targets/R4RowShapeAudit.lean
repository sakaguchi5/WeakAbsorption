import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4AtomAudit
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4RowProfileFamily
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowShape

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity

/--
Forget one audited `RowShapeCoord` to one Semantics3 coarse coordinate.
This is the shape-level analogue of `atomToShapeCoord`.
-/
def rowShapeCoordToObserved (c : RowShapeCoord) : ObservedShapeCoord :=
  { kind := atomToRuleKind c.1
    side := atomToSide c.2 }

/--
Semantics3 readout of the audited R4 target-level row shape.
-/
def observedRowShapeOfTarget (tg : ObservedTarget) : List ObservedShapeCoord :=
  (rowShapeOfTarget tg).map rowShapeCoordToObserved

/--
State-level version of the same readout.
-/
def observedRowShapeOfState (σ : ObservedState) : List ObservedShapeCoord :=
  observedRowShapeOfTarget (stateTarget σ)

theorem observedRowShapeOfTarget_eq_map_rowShapeOfTarget
    (tg : ObservedTarget) :
    observedRowShapeOfTarget tg =
      (rowShapeOfTarget tg).map rowShapeCoordToObserved := by
  rfl

theorem observedRowShapeOfState_eq_map_rowShapeOfState
    (σ : ObservedState) :
    observedRowShapeOfState σ =
      (rowShapeOfState σ).map rowShapeCoordToObserved := by
  rfl

/--
The audited row-shape readout agrees with the existing Semantics3 row-shape.
-/
theorem observedRowShapeOfTarget_eq_observedRowShape
    (tg : ObservedTarget) :
    observedRowShapeOfTarget tg = observedRowShape tg := by
  cases tg <;> native_decide

/--
State-level version of the same agreement theorem.
-/
theorem observedRowShapeOfState_eq_observedRowShape
    (σ : ObservedState) :
    observedRowShapeOfState σ = observedRowShape (stateTarget σ) := by
  cases σ <;> native_decide

/--
The audited row-shape readout factors through exact atoms via `rowProfileOfAtoms`.
-/
theorem observedRowShapeOfTarget_factors_through_exact_atoms
    (tg : ObservedTarget) :
    observedRowShapeOfTarget tg =
      (rowProfileOfAtoms (rowAtomsOfTarget tg)).support := by
  calc
    observedRowShapeOfTarget tg
        = observedRowShape tg := observedRowShapeOfTarget_eq_observedRowShape tg
    _ = (observedRowProfile tg).support := by
          simpa using observedRowShape_factors_through_rowProfile tg
    _ = (rowProfileOfAtoms (rowAtomsOfTarget tg)).support := by
          rw [(rowProfileOfTargetAtoms_eq_observedRowProfile tg).symm]

/--
State-level version of the same factorization theorem.
-/
theorem observedRowShapeOfState_factors_through_exact_atoms
    (σ : ObservedState) :
    observedRowShapeOfState σ =
      (rowProfileOfAtoms (rowAtomsOfState σ)).support := by
  calc
    observedRowShapeOfState σ
        = observedRowShape (stateTarget σ) := observedRowShapeOfState_eq_observedRowShape σ
    _ = (observedRowProfile (stateTarget σ)).support := by
          simpa using observedRowShape_factors_through_rowProfile (stateTarget σ)
    _ = (rowProfileOfAtoms (rowAtomsOfState σ)).support := by
          rw [(rowProfileOfStateAtoms_eq_observedRowProfile σ).symm]

/--
Semantics3 `sameCoordDuplication` matches the audited R4 shape notion exactly.
-/
theorem observedShapeFamily_eq_sameCoordDuplication_iff
    (tg : ObservedTarget) :
    observedShapeFamily tg = .sameCoordDuplication
      ↔ SameSlotSameChannelDuplication tg := by
  cases tg <;> native_decide

/--
Semantics3 `rootMixedPure` matches the audited R4 shape notion exactly.
-/
theorem observedShapeFamily_eq_rootMixedPure_iff
    (tg : ObservedTarget) :
    observedShapeFamily tg = .rootMixedPure
      ↔ RootMixedPureShape tg := by
  cases tg <;> native_decide

/--
Semantics3 `bridgeSplitMixed` matches the audited R4 shape notion exactly.
-/
theorem observedShapeFamily_eq_bridgeSplitMixed_iff
    (tg : ObservedTarget) :
    observedShapeFamily tg = .bridgeSplitMixed
      ↔ BridgeSplitMixedShape tg := by
  cases tg <;> native_decide

/--
Hence `singleton` is exactly the residual audited case:
not duplicated, not root-mixed pure, not bridge-split mixed.
-/
theorem observedShapeFamily_eq_singleton_iff
    (tg : ObservedTarget) :
    observedShapeFamily tg = .singleton
      ↔ ¬ SameSlotSameChannelDuplication tg
        ∧ ¬ RootMixedPureShape tg
        ∧ ¬ BridgeSplitMixedShape tg := by
  cases tg <;> native_decide

/--
Current audited R4 still separates pure two-atom and bridge-split two-atom
at the row-shape level, even though both have atom-count 2.
-/
theorem pure_and_bridgeSplit_separated_by_observedRowShape :
    ∃ tgPure tgBridge : ObservedTarget,
      observedRegime tgPure = .pure
      ∧ observedRegime tgBridge = .bridgeSplit
      ∧ observedAtomCount tgPure = 2
      ∧ observedAtomCount tgBridge = 2
      ∧ observedRowShape tgPure ≠ observedRowShape tgBridge := by
  refine ⟨.nfXASqAPred, .nfUDecorRightPred, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
AA-right and AA-leftLift are both shape-collapsed pure 2-edge cases,
but their observed row-shapes still differ by side.
-/
theorem aa_right_leftLift_observedRowShape_distinct :
    observedRowShape .nfXASqAPred ≠ observedRowShape .nfUSqLiftAPred := by
  decide

/--
Hole-root and DecorHole-root are both root-mixed pure, but their
observed row-shapes differ by the second root coordinate kind.
-/
theorem hole_root_decorHole_root_observedRowShape_distinct :
    observedRowShape .nfUHolePred ≠ observedRowShape .nfUDecorHolePred := by
  decide

/--
Bridge-split remains separated from the AA-right collapsed pure shape.
-/
theorem bridgeSplit_observedRowShape_ne_aa_right :
    observedRowShape .nfUDecorRightPred ≠ observedRowShape .nfXASqAPred := by
  decide

/--
Bridge-split remains separated from the hole-root pure shape.
-/
theorem bridgeSplit_observedRowShape_ne_hole_root :
    observedRowShape .nfUDecorRightPred ≠ observedRowShape .nfUHolePred := by
  decide

/--
Summary: Semantics3 row-shape is the audited coarse readout of the exact
R4 row-shape sector, and the current shape-family labels agree with the
audited R4 shape catalog.
-/
theorem observedRowShape_and_shapeFamily_are_audited :
    (∀ tg : ObservedTarget,
      observedRowShapeOfTarget tg = observedRowShape tg)
    ∧
    (∀ tg : ObservedTarget,
      observedShapeFamily tg = .sameCoordDuplication
        ↔ SameSlotSameChannelDuplication tg)
    ∧
    (∀ tg : ObservedTarget,
      observedShapeFamily tg = .rootMixedPure
        ↔ RootMixedPureShape tg)
    ∧
    (∀ tg : ObservedTarget,
      observedShapeFamily tg = .bridgeSplitMixed
        ↔ BridgeSplitMixedShape tg) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tg
    exact observedRowShapeOfTarget_eq_observedRowShape tg
  · intro tg
    exact observedShapeFamily_eq_sameCoordDuplication_iff tg
  · intro tg
    exact observedShapeFamily_eq_rootMixedPure_iff tg
  · intro tg
    exact observedShapeFamily_eq_bridgeSplitMixed_iff tg

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
