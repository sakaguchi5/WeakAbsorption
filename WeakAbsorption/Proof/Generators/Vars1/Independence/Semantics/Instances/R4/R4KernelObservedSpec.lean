import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowShape

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Instances
namespace R4

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section ObservedSpec

inductive ObservedShapeFamily where
  | singleton
  | sameSlotSameChannelDuplication
  | rootMixedPure
  | bridgeSplitMixed
deriving DecidableEq, Repr

structure ObservedKernelSnapshot where
  kernel      : CoreKernelClass
  shell       : CoreKernelShell
  state       : CoreRealizedState
  regime      : CoreKernelRegime
  rowAtoms    : List RowAtom
  rowShape    : List RowShapeCoord
  atomCount   : Nat
  shapeCount  : Nat
  shapeFamily : ObservedShapeFamily
deriving DecidableEq, Repr

def observedKernel : CoreKernelTarget -> CoreKernelClass
  | .nfXASqRightPred        => .saKernel
  | .nfUSqLiftRightSPred    => .saKernel
  | .nfXADecorRightPred     => .decorRightKernel
  | .nfUDecorLiftRightSPred => .decorRightKernel
  | .nfXADecorLeftPred      => .decorLeftKernel
  | .nfUDecorLiftLeftSPred  => .decorLeftKernel
  | .nfUStablePred          => .stableKernel
  | .nfUHolePred            => .holeKernel
  | .nfUDecorHolePred       => .decorHoleKernel
  | .nfXASqAPred            => .aaKernel
  | .nfUSqLiftAPred         => .aaKernel
  | .nfUDecorRightPred      => .bridgeKernel

def observedShell : CoreKernelTarget -> CoreKernelShell
  | .nfXASqRightPred        => .rightShell
  | .nfUSqLiftRightSPred    => .leftLift
  | .nfXADecorRightPred     => .rightShell
  | .nfUDecorLiftRightSPred => .leftLift
  | .nfXADecorLeftPred      => .rightShell
  | .nfUDecorLiftLeftSPred  => .leftLift
  | .nfUStablePred          => .leftLift
  | .nfUHolePred            => .rootShell
  | .nfUDecorHolePred       => .rootShell
  | .nfXASqAPred            => .rightShell
  | .nfUSqLiftAPred         => .leftLift
  | .nfUDecorRightPred      => .bridgeSplitShell

def observedState : CoreKernelTarget -> CoreRealizedState
  | .nfXASqRightPred        => .saRight
  | .nfUSqLiftRightSPred    => .saLeftLift
  | .nfXADecorRightPred     => .decorRight_right
  | .nfUDecorLiftRightSPred => .decorRight_leftLift
  | .nfXADecorLeftPred      => .decorLeft_right
  | .nfUDecorLiftLeftSPred  => .decorLeft_leftLift
  | .nfUStablePred          => .stable_leftLift
  | .nfUHolePred            => .hole_root
  | .nfUDecorHolePred       => .decorHole_root
  | .nfXASqAPred            => .aa_right
  | .nfUSqLiftAPred         => .aa_leftLift
  | .nfUDecorRightPred      => .bridge_split

def observedRegime : CoreKernelTarget -> CoreKernelRegime
  | .nfUDecorRightPred => .bridgeSplit
  | _ => .pure

def observedRowAtoms : CoreKernelTarget -> List RowAtom
  | .nfXASqRightPred =>
      [ { slot := .sqAbsorb, channel := .right, tag := .nfXA } ]
  | .nfUSqLiftRightSPred =>
      [ { slot := .sqAbsorb, channel := .left, tag := .nfU } ]
  | .nfXADecorRightPred =>
      [ { slot := .decor, channel := .right, tag := .nfXA } ]
  | .nfUDecorLiftRightSPred =>
      [ { slot := .decor, channel := .left, tag := .nfU } ]
  | .nfXADecorLeftPred =>
      [ { slot := .decor, channel := .right, tag := .nfXA } ]
  | .nfUDecorLiftLeftSPred =>
      [ { slot := .decor, channel := .left, tag := .nfU } ]
  | .nfUStablePred =>
      [ { slot := .sqStable, channel := .left, tag := .nfU } ]
  | .nfUHolePred =>
      [ { slot := .sqAbsorb, channel := .root, tag := .nfU }
      , { slot := .c2c1,     channel := .root, tag := .nfU } ]
  | .nfUDecorHolePred =>
      [ { slot := .sqAbsorb, channel := .root, tag := .nfUHolePred }
      , { slot := .decor,    channel := .root, tag := .nfU } ]
  | .nfXASqAPred =>
      [ { slot := .sqAbsorb, channel := .right, tag := .nfXA }
      , { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred } ]
  | .nfUSqLiftAPred =>
      [ { slot := .sqAbsorb, channel := .left, tag := .nfU }
      , { slot := .sqAbsorb, channel := .left, tag := .nfUSqLiftRightPred } ]
  | .nfUDecorRightPred =>
      [ { slot := .sqAbsorb, channel := .left,  tag := .nfM }
      , { slot := .decor,    channel := .right, tag := .nfU } ]

def observedRowShape : CoreKernelTarget -> List RowShapeCoord
  | .nfXASqRightPred        => [(.sqAbsorb, .right)]
  | .nfUSqLiftRightSPred    => [(.sqAbsorb, .left)]
  | .nfXADecorRightPred     => [(.decor, .right)]
  | .nfUDecorLiftRightSPred => [(.decor, .left)]
  | .nfXADecorLeftPred      => [(.decor, .right)]
  | .nfUDecorLiftLeftSPred  => [(.decor, .left)]
  | .nfUStablePred          => [(.sqStable, .left)]
  | .nfUHolePred            => [(.sqAbsorb, .root), (.c2c1, .root)]
  | .nfUDecorHolePred       => [(.sqAbsorb, .root), (.decor, .root)]
  | .nfXASqAPred            => [(.sqAbsorb, .right)]
  | .nfUSqLiftAPred         => [(.sqAbsorb, .left)]
  | .nfUDecorRightPred      => [(.sqAbsorb, .left), (.decor, .right)]

def observedShapeFamily : CoreKernelTarget -> ObservedShapeFamily
  | .nfUHolePred            => .rootMixedPure
  | .nfUDecorHolePred       => .rootMixedPure
  | .nfXASqAPred            => .sameSlotSameChannelDuplication
  | .nfUSqLiftAPred         => .sameSlotSameChannelDuplication
  | .nfUDecorRightPred      => .bridgeSplitMixed
  | _                       => .singleton

def observedSnapshot (tg : CoreKernelTarget) : ObservedKernelSnapshot :=
  { kernel := observedKernel tg
    shell := observedShell tg
    state := observedState tg
    regime := observedRegime tg
    rowAtoms := observedRowAtoms tg
    rowShape := observedRowShape tg
    atomCount := (observedRowAtoms tg).length
    shapeCount := (observedRowShape tg).length
    shapeFamily := observedShapeFamily tg }

/-- Frozen cardinalities of the current right-branch semantics. -/
def observedVertexCount : Nat := 13
def observedDistinctEdgeSupportCount : Nat := 10

theorem package_kernel_matches_observed (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).kernel = observedKernel tg := by
  cases tg <;> rfl

theorem package_shell_matches_observed (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).shell = observedShell tg := by
  cases tg <;> rfl

theorem package_state_matches_observed (tg : CoreKernelTarget) :
    packageState tg = observedState tg := by
  cases tg <;> rfl

theorem package_regime_matches_observed (tg : CoreKernelTarget) :
    packageRegime tg = observedRegime tg := by
  cases tg <;> rfl

theorem rowAtoms_matches_observed (tg : CoreKernelTarget) :
    rowAtomsOfTarget tg = observedRowAtoms tg := by
  cases tg <;> decide

theorem rowShape_matches_observed (tg : CoreKernelTarget) :
    rowShapeOfTarget tg = observedRowShape tg := by
  cases tg <;> decide

theorem atomCount_matches_observed (tg : CoreKernelTarget) :
    (r4ExactRowMultiHypergraph.edgeSupport tg).length = (observedSnapshot tg).atomCount := by
  cases tg <;> decide

theorem shapeCount_matches_observed (tg : CoreKernelTarget) :
    (rowShapeOfTarget tg).length = (observedSnapshot tg).shapeCount := by
  cases tg <;> decide

theorem observedRowAtoms_sound (tg : CoreKernelTarget) :
    rowAtomsOfTarget tg = observedRowAtoms tg := by
  cases tg <;> rfl

theorem observedRowShape_sound (tg : CoreKernelTarget) :
    rowShapeOfTarget tg = observedRowShape tg := by
  cases tg <;> rfl

theorem observedShapeFamily_sound (tg : CoreKernelTarget) :
    match observedShapeFamily tg with
    | .singleton =>
        (r4ExactRowMultiHypergraph.edgeSupport tg).length = 1 ∧
        (rowShapeOfTarget tg).length = 1
    | .sameSlotSameChannelDuplication =>
        SameSlotSameChannelDuplication tg
    | .rootMixedPure =>
        RootMixedPureShape tg
    | .bridgeSplitMixed =>
        BridgeSplitMixedShape tg := by
  cases tg with
  | nfXASqRightPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfXASqRightPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfXASqRightPred)
  | nfUSqLiftRightSPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfUSqLiftRightSPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfUSqLiftRightSPred)
  | nfXADecorRightPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfXADecorRightPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfXADecorRightPred)
  | nfUDecorLiftRightSPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfUDecorLiftRightSPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfUDecorLiftRightSPred)
  | nfXADecorLeftPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfXADecorLeftPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfXADecorLeftPred)
  | nfUDecorLiftLeftSPred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfUDecorLiftLeftSPred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfUDecorLiftLeftSPred)
  | nfUStablePred =>
      refine ⟨?_, ?_⟩
      · simpa [observedRowAtoms, r4ExactRowMultiHypergraph, r4ExactRowEdgeSupport] using
          congrArg List.length (rowAtoms_matches_observed .nfUStablePred)
      · simpa [observedRowShape] using
          congrArg List.length (rowShape_matches_observed .nfUStablePred)
  | nfUHolePred =>
      simpa [observedShapeFamily] using hole_root_rootMixedPureShape
  | nfUDecorHolePred =>
      simpa [observedShapeFamily] using decorHole_root_rootMixedPureShape
  | nfXASqAPred =>
      simpa [observedShapeFamily] using aa_right_sameSlotSameChannelDuplication
  | nfUSqLiftAPred =>
      simpa [observedShapeFamily] using aa_leftLift_sameSlotSameChannelDuplication
  | nfUDecorRightPred =>
      simpa [observedShapeFamily] using bridge_split_mixed_shape

theorem current_snapshot_matches_observed (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).kernel = (observedSnapshot tg).kernel ∧
    (r4SemanticPackageOf tg).shell = (observedSnapshot tg).shell ∧
    packageState tg = (observedSnapshot tg).state ∧
    packageRegime tg = (observedSnapshot tg).regime ∧
    rowAtomsOfTarget tg = (observedSnapshot tg).rowAtoms ∧
    rowShapeOfTarget tg = (observedSnapshot tg).rowShape ∧
    (r4ExactRowMultiHypergraph.edgeSupport tg).length = (observedSnapshot tg).atomCount ∧
    (rowShapeOfTarget tg).length = (observedSnapshot tg).shapeCount := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact package_kernel_matches_observed tg
  · exact package_shell_matches_observed tg
  · exact package_state_matches_observed tg
  · exact package_regime_matches_observed tg
  · exact rowAtoms_matches_observed tg
  · exact rowShape_matches_observed tg
  · exact atomCount_matches_observed tg
  · exact shapeCount_matches_observed tg

theorem vertexCount_matches_observed :
    exactRowAtomUniverse.length = observedVertexCount := by
  decide

theorem distinctEdgeSupportCount_matches_observed :
    r4DistinctEdgeSupports.length = observedDistinctEdgeSupportCount := by
  decide

end ObservedSpec

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
