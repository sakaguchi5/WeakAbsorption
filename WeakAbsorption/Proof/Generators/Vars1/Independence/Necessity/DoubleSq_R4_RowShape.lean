import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowHypergraph

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section RowShape

/-- Coarse row-shape coordinates forget tags and keep only slot × channel incidence. -/
abbrev RowShapeCoord := RowSlot × CtxChannel

/-- Shape readout for realized states, via the forgetful map to public targets. -/
def rowShapeOfState (σ : CoreRealizedState) : List RowShapeCoord :=
  rowShapeOfTarget (stateTarget σ)

theorem rowShapeOfState_eq (σ : CoreRealizedState) :
    rowShapeOfState σ = rowShapeOfTarget (stateTarget σ) := by
  rfl

/-- Canonical singleton / mixed shapes used in the R4 right-branch catalog. -/
abbrev sh_sqAbsorb_right  : List RowShapeCoord := [(.sqAbsorb, .right)]
abbrev sh_sqAbsorb_left   : List RowShapeCoord := [(.sqAbsorb, .left)]
abbrev sh_decor_right     : List RowShapeCoord := [(.decor,    .right)]
abbrev sh_decor_left      : List RowShapeCoord := [(.decor,    .left)]
abbrev sh_sqStable_left   : List RowShapeCoord := [(.sqStable, .left)]

abbrev sh_hole_root       : List RowShapeCoord := [(.sqAbsorb, .root), (.c2c1,  .root)]
abbrev sh_decorHole_root  : List RowShapeCoord := [(.sqAbsorb, .root), (.decor, .root)]
abbrev sh_bridge_split    : List RowShapeCoord := [(.sqAbsorb, .left), (.decor, .right)]

/-- One-atom shape readout. -/
theorem rowShape_nfXASqRightPred_one_atom        : rowShapeOfTarget .nfXASqRightPred       = sh_sqAbsorb_right := by decide
theorem rowShape_nfUSqLiftRightSPred_one_atom    : rowShapeOfTarget .nfUSqLiftRightSPred   = sh_sqAbsorb_left  := by decide
theorem rowShape_nfXADecorRightPred_one_atom     : rowShapeOfTarget .nfXADecorRightPred    = sh_decor_right    := by decide
theorem rowShape_nfUDecorLiftRightSPred_one_atom : rowShapeOfTarget .nfUDecorLiftRightSPred= sh_decor_left     := by decide
theorem rowShape_nfXADecorLeftPred_one_atom      : rowShapeOfTarget .nfXADecorLeftPred     = sh_decor_right    := by decide
theorem rowShape_nfUDecorLiftLeftSPred_one_atom  : rowShapeOfTarget .nfUDecorLiftLeftSPred = sh_decor_left     := by decide
theorem rowShape_nfUStablePred_one_atom          : rowShapeOfTarget .nfUStablePred         = sh_sqStable_left  := by decide

/-- Two-atom readout in the extensional shape language. -/
theorem rowShape_aa_right        : rowShapeOfTarget .nfXASqAPred     = sh_sqAbsorb_right  := by decide
theorem rowShape_aa_leftLift     : rowShapeOfTarget .nfUSqLiftAPred  = sh_sqAbsorb_left   := by decide
theorem rowShape_hole_root       : rowShapeOfTarget .nfUHolePred     = sh_hole_root       := by decide
theorem rowShape_decorHole_root  : rowShapeOfTarget .nfUDecorHolePred = sh_decorHole_root  := by decide
theorem rowShape_bridge_split    : rowShapeOfTarget .nfUDecorRightPred = sh_bridge_split    := by decide

/-- Two-atomic but shape-collapsed: both atoms live in one slot/channel coordinate. -/
def SameSlotSameChannelDuplication (tg : CoreKernelTarget) : Prop :=
  (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2 ∧
  (rowShapeOfTarget tg).length = 1

/-- Two-atomic and root-mixed: two distinct root coordinates occur. -/
def RootMixedPureShape (tg : CoreKernelTarget) : Prop :=
  packageRegime tg = .pure ∧
  (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2 ∧
  (rowShapeOfTarget tg).length = 2 ∧
  ∀ sc, sc ∈ rowShapeOfTarget tg → sc.2 = .root

/-- The unique bridge-split shape mixes left sqAbsorb with right decor. -/
def BridgeSplitMixedShape (tg : CoreKernelTarget) : Prop :=
  packageRegime tg = .bridgeSplit ∧
  rowShapeOfTarget tg = sh_bridge_split

instance instDecidableSameSlotSameChannelDuplication (tg : CoreKernelTarget) :
    Decidable (SameSlotSameChannelDuplication tg) := by
  classical
  unfold SameSlotSameChannelDuplication
  infer_instance

instance instDecidableRootMixedPureShape (tg : CoreKernelTarget) :
    Decidable (RootMixedPureShape tg) := by
  classical
  unfold RootMixedPureShape
  infer_instance

instance instDecidableBridgeSplitMixedShape (tg : CoreKernelTarget) :
    Decidable (BridgeSplitMixedShape tg) := by
  classical
  unfold BridgeSplitMixedShape
  infer_instance

/-- The AA-right pure 2-edge collapses to one shape coordinate. -/
theorem aa_right_sameSlotSameChannelDuplication :
    SameSlotSameChannelDuplication .nfXASqAPred := by
  decide

/-- The AA-leftLift pure 2-edge also collapses to one shape coordinate. -/
theorem aa_leftLift_sameSlotSameChannelDuplication :
    SameSlotSameChannelDuplication .nfUSqLiftAPred := by
  decide

/-- Hole-root is pure, 2-atomic, and root-mixed. -/
theorem hole_root_rootMixedPureShape :
    RootMixedPureShape .nfUHolePred := by
  decide

/-- DecorHole-root is pure, 2-atomic, and root-mixed. -/
theorem decorHole_root_rootMixedPureShape :
    RootMixedPureShape .nfUDecorHolePred := by
  decide

/-- Bridge-split has its own mixed left/right cross-slot shape. -/
theorem bridge_split_mixed_shape :
    BridgeSplitMixedShape .nfUDecorRightPred := by
  decide

/-- The bridge-split target is 2-atomic but does not collapse to one shape coordinate. -/
theorem bridge_split_not_sameSlotSameChannelDuplication :
    ¬ SameSlotSameChannelDuplication .nfUDecorRightPred := by
  decide

/-- The bridge-split target is not root-mixed. -/
theorem bridge_split_not_rootMixedPureShape :
    ¬ RootMixedPureShape .nfUDecorRightPred := by
  decide

/-- Hence cardinality 2 does not determine the regime; shape still separates cases. -/
theorem two_atom_pure_and_bridge_split_separated_by_shape :
    ∃ tgPure tgBridge : CoreKernelTarget,
      packageRegime tgPure = .pure ∧
      packageRegime tgBridge = .bridgeSplit ∧
      (r4ExactRowMultiHypergraph.edgeSupport tgPure).length = 2 ∧
      (r4ExactRowMultiHypergraph.edgeSupport tgBridge).length = 2 ∧
      rowShapeOfTarget tgPure ≠ rowShapeOfTarget tgBridge := by
  refine ⟨.nfXASqAPred, .nfUDecorRightPred, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- AA-right and AA-leftLift are both pure 2-edges, but their collapsed coordinates differ by channel. -/
theorem aa_right_leftLift_shape_distinct :
    rowShapeOfTarget .nfXASqAPred ≠ rowShapeOfTarget .nfUSqLiftAPred := by
  decide

/-- Hole-root and DecorHole-root are both root-mixed, but their second root slot differs. -/
theorem hole_root_decorHole_root_shape_distinct :
    rowShapeOfTarget .nfUHolePred ≠ rowShapeOfTarget .nfUDecorHolePred := by
  decide

/-- Bridge-split is distinct from the AA collapsed pure shape. -/
theorem bridge_split_shape_ne_aa_right_shape :
    rowShapeOfTarget .nfUDecorRightPred ≠ rowShapeOfTarget .nfXASqAPred := by
  decide

/-- Bridge-split is distinct from the hole-root pure shape. -/
theorem bridge_split_shape_ne_hole_root_shape :
    rowShapeOfTarget .nfUDecorRightPred ≠ rowShapeOfTarget .nfUHolePred := by
  decide

private theorem shape_classify_nfXASqAPred_two_atom :
    (packageRegime CoreKernelTarget.nfXASqAPred = .bridgeSplit ↔
      BridgeSplitMixedShape CoreKernelTarget.nfXASqAPred) ∧
    (packageRegime CoreKernelTarget.nfXASqAPred = .pure ↔
      SameSlotSameChannelDuplication CoreKernelTarget.nfXASqAPred ∨
      RootMixedPureShape CoreKernelTarget.nfXASqAPred) := by
  constructor
  · apply Iff.intro
    · intro h
      exfalso
      have hnot : ¬ packageRegime CoreKernelTarget.nfXASqAPred = .bridgeSplit := by
        decide
      exact hnot h
    · intro h
      exact h.1
  · apply Iff.intro
    · intro h
      have hs : SameSlotSameChannelDuplication CoreKernelTarget.nfXASqAPred := by
        decide
      exact Or.inl hs
    · intro h
      have hp : packageRegime CoreKernelTarget.nfXASqAPred = .pure := by
        decide
      exact hp

private theorem shape_classify_nfUSqLiftAPred_two_atom :
    (packageRegime CoreKernelTarget.nfUSqLiftAPred = .bridgeSplit ↔
      BridgeSplitMixedShape CoreKernelTarget.nfUSqLiftAPred) ∧
    (packageRegime CoreKernelTarget.nfUSqLiftAPred = .pure ↔
      SameSlotSameChannelDuplication CoreKernelTarget.nfUSqLiftAPred ∨
      RootMixedPureShape CoreKernelTarget.nfUSqLiftAPred) := by
  constructor
  · apply Iff.intro
    · intro h
      exfalso
      have hnot : ¬ packageRegime CoreKernelTarget.nfUSqLiftAPred = .bridgeSplit := by
        decide
      exact hnot h
    · intro h
      exact h.1
  · apply Iff.intro
    · intro h
      have hs : SameSlotSameChannelDuplication CoreKernelTarget.nfUSqLiftAPred := by
        decide
      exact Or.inl hs
    · intro h
      have hp : packageRegime CoreKernelTarget.nfUSqLiftAPred = .pure := by
        decide
      exact hp

private theorem shape_classify_nfUHolePred_two_atom :
    (packageRegime CoreKernelTarget.nfUHolePred = .bridgeSplit ↔
      BridgeSplitMixedShape CoreKernelTarget.nfUHolePred) ∧
    (packageRegime CoreKernelTarget.nfUHolePred = .pure ↔
      SameSlotSameChannelDuplication CoreKernelTarget.nfUHolePred ∨
      RootMixedPureShape CoreKernelTarget.nfUHolePred) := by
  constructor
  · apply Iff.intro
    · intro h
      exfalso
      have hnot : ¬ packageRegime CoreKernelTarget.nfUHolePred = .bridgeSplit := by
        decide
      exact hnot h
    · intro h
      exact h.1
  · apply Iff.intro
    · intro h
      have hr : RootMixedPureShape CoreKernelTarget.nfUHolePred := by
        decide
      exact Or.inr hr
    · intro h
      have hp : packageRegime CoreKernelTarget.nfUHolePred = .pure := by
        decide
      exact hp

private theorem shape_classify_nfUDecorHolePred_two_atom :
    (packageRegime CoreKernelTarget.nfUDecorHolePred = .bridgeSplit ↔
      BridgeSplitMixedShape CoreKernelTarget.nfUDecorHolePred) ∧
    (packageRegime CoreKernelTarget.nfUDecorHolePred = .pure ↔
      SameSlotSameChannelDuplication CoreKernelTarget.nfUDecorHolePred ∨
      RootMixedPureShape CoreKernelTarget.nfUDecorHolePred) := by
  constructor
  · apply Iff.intro
    · intro h
      exfalso
      have hnot : ¬ packageRegime CoreKernelTarget.nfUDecorHolePred = .bridgeSplit := by
        decide
      exact hnot h
    · intro h
      exact h.1
  · apply Iff.intro
    · intro h
      have hr : RootMixedPureShape CoreKernelTarget.nfUDecorHolePred := by
        decide
      exact Or.inr hr
    · intro h
      have hp : packageRegime CoreKernelTarget.nfUDecorHolePred = .pure := by
        decide
      exact hp

private theorem shape_classify_nfUDecorRightPred_two_atom :
    (packageRegime CoreKernelTarget.nfUDecorRightPred = .bridgeSplit ↔
      BridgeSplitMixedShape CoreKernelTarget.nfUDecorRightPred) ∧
    (packageRegime CoreKernelTarget.nfUDecorRightPred = .pure ↔
      SameSlotSameChannelDuplication CoreKernelTarget.nfUDecorRightPred ∨
      RootMixedPureShape CoreKernelTarget.nfUDecorRightPred) := by
  constructor
  · apply Iff.intro
    · intro h
      have hb : BridgeSplitMixedShape CoreKernelTarget.nfUDecorRightPred := by
        decide
      exact hb
    · intro h
      exact h.1
  · apply Iff.intro
    · intro h
      exfalso
      have hnot : ¬ packageRegime CoreKernelTarget.nfUDecorRightPred = .pure := by
        decide
      exact hnot h
    · intro h
      exfalso
      have hnot :
          ¬ (SameSlotSameChannelDuplication CoreKernelTarget.nfUDecorRightPred ∨
              RootMixedPureShape CoreKernelTarget.nfUDecorRightPred) := by
        decide
      exact hnot h

theorem two_atom_shape_classification (tg : CoreKernelTarget)
    (h2 : (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2) :
    (packageRegime tg = .bridgeSplit ↔ BridgeSplitMixedShape tg) ∧
    (packageRegime tg = .pure ↔
      SameSlotSameChannelDuplication tg ∨ RootMixedPureShape tg) := by
  cases tg
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXASqRightPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUSqLiftRightSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXADecorRightPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorLiftRightSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXADecorLeftPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorLiftLeftSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUStablePred).length = 2) := by
      decide
    exact hnot h2
  · simpa using shape_classify_nfUHolePred_two_atom
  · simpa using shape_classify_nfUDecorHolePred_two_atom
  · simpa using shape_classify_nfXASqAPred_two_atom
  · simpa using shape_classify_nfUSqLiftAPred_two_atom
  · simpa using shape_classify_nfUDecorRightPred_two_atom

theorem two_atom_regime_classification (tg : CoreKernelTarget)
    (h2 : (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2) :
    SameSlotSameChannelDuplication tg ∨
    RootMixedPureShape tg ∨
    BridgeSplitMixedShape tg := by
  have hcls := two_atom_shape_classification tg h2
  rcases hcls with ⟨hbridge, hpure⟩
  by_cases hb : packageRegime tg = .bridgeSplit
  · exact Or.inr (Or.inr (hbridge.mp hb))
  · have hp : packageRegime tg = .pure := by
      cases hreg : packageRegime tg <;> simp_all
    have hshape : SameSlotSameChannelDuplication tg ∨ RootMixedPureShape tg := hpure.mp hp
    rcases hshape with hs | hr
    · exact Or.inl hs
    · exact Or.inr (Or.inl hr)

end RowShape

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
