import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Core.Main

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

private def coord (kind : ObservedRuleKind) (side : ObservedSide) : ObservedShapeCoord :=
  ObservedShapeCoord.mkCoord kind side

private def profile1 (kind : ObservedRuleKind) (side : ObservedSide) : ObservedRowProfile :=
  ObservedRowProfile.singleton kind side

private def profile2
    (aKind : ObservedRuleKind) (aSide : ObservedSide)
    (bKind : ObservedRuleKind) (bSide : ObservedSide) : ObservedRowProfile :=
  ObservedRowProfile.ofCounts
    [ (coord aKind aSide, 1)
    , (coord bKind bSide, 1)
    ]

private def dupProfile (kind : ObservedRuleKind) (side : ObservedSide) : ObservedRowProfile :=
  ObservedRowProfile.ofCounts
    [ (coord kind side, 2) ]

/-- Target-level observed kernel label. -/
def observedKernel : ObservedTarget → ObservedKernelClass
  | .nfXASqRightPred         => .saKernel
  | .nfUSqLiftRightSPred     => .saKernel
  | .nfXADecorRightPred      => .decorRightKernel
  | .nfUDecorLiftRightSPred  => .decorRightKernel
  | .nfXADecorLeftPred       => .decorLeftKernel
  | .nfUDecorLiftLeftSPred   => .decorLeftKernel
  | .nfUStablePred           => .stableKernel
  | .nfUHolePred             => .holeKernel
  | .nfUDecorHolePred        => .decorHoleKernel
  | .nfXASqAPred             => .aaKernel
  | .nfUSqLiftAPred          => .aaKernel
  | .nfUDecorRightPred       => .bridgeKernel

/-- Target-level observed shell label. -/
def observedShell : ObservedTarget → ObservedShellKind
  | .nfXASqRightPred         => .rightShell
  | .nfUSqLiftRightSPred     => .leftLift
  | .nfXADecorRightPred      => .rightShell
  | .nfUDecorLiftRightSPred  => .leftLift
  | .nfXADecorLeftPred       => .rightShell
  | .nfUDecorLiftLeftSPred   => .leftLift
  | .nfUStablePred           => .leftLift
  | .nfUHolePred             => .rootShell
  | .nfUDecorHolePred        => .rootShell
  | .nfXASqAPred             => .rightShell
  | .nfUSqLiftAPred          => .leftLift
  | .nfUDecorRightPred       => .bridgeSplitShell

/-- Target-level observed realized state. -/
def observedState : ObservedTarget → ObservedState
  | .nfXASqRightPred         => .saRight
  | .nfUSqLiftRightSPred     => .saLeftLift
  | .nfXADecorRightPred      => .decorRight_right
  | .nfUDecorLiftRightSPred  => .decorRight_leftLift
  | .nfXADecorLeftPred       => .decorLeft_right
  | .nfUDecorLiftLeftSPred   => .decorLeft_leftLift
  | .nfUStablePred           => .stable_leftLift
  | .nfUHolePred             => .hole_root
  | .nfUDecorHolePred        => .decorHole_root
  | .nfXASqAPred             => .aa_right
  | .nfUSqLiftAPred          => .aa_leftLift
  | .nfUDecorRightPred       => .bridge_split

/-- Target-label sector bundled as a first-class object. -/
def observedLabels (tg : ObservedTarget) : ObservedTargetLabels :=
  { kernel := observedKernel tg
    shell := observedShell tg
    state := observedState tg }

/-- Target-level observed regime. -/
def observedRegime : ObservedTarget → ObservedRegime
  | .nfUDecorRightPred => .bridgeSplit
  | _                  => .pure

/--
Multiplicity-aware row profile.

This is the row-geometry core object for Semantics3 stage 1:
- no legacy exact-row atoms
- no legacy tag vocabulary
- only coarse rule-kind × side with multiplicity
-/
def observedRowProfile : ObservedTarget → ObservedRowProfile
  | .nfXASqRightPred         => profile1 .sqAbsorb .right
  | .nfUSqLiftRightSPred     => profile1 .sqAbsorb .left
  | .nfXADecorRightPred      => profile1 .decor .right
  | .nfUDecorLiftRightSPred  => profile1 .decor .left
  | .nfXADecorLeftPred       => profile1 .decor .right
  | .nfUDecorLiftLeftSPred   => profile1 .decor .left
  | .nfUStablePred           => profile1 .sqStable .left
  | .nfUHolePred             => profile2 .sqAbsorb .root .c2c1 .root
  | .nfUDecorHolePred        => profile2 .sqAbsorb .root .decor .root
  | .nfXASqAPred             => dupProfile .sqAbsorb .right
  | .nfUSqLiftAPred          => dupProfile .sqAbsorb .left
  | .nfUDecorRightPred       => profile2 .sqAbsorb .left .decor .right

/-- Row-geometry sector bundled as a first-class object. -/
def observedGeometry (tg : ObservedTarget) : ObservedRowGeometry :=
  { rowProfile := observedRowProfile tg }

/--
Current coarse family attached to each target.

We intentionally keep this as a separate field for now.
The next compression step is to show this factors through `observedRowProfile`.
-/
def observedShapeFamily : ObservedTarget → ObservedShapeFamily
  | .nfUHolePred            => .rootMixedPure
  | .nfUDecorHolePred       => .rootMixedPure
  | .nfXASqAPred            => .sameCoordDuplication
  | .nfUSqLiftAPred         => .sameCoordDuplication
  | .nfUDecorRightPred      => .bridgeSplitMixed
  | _                       => .singleton

def observedSnapshot (tg : ObservedTarget) : ObservedKernelSnapshot :=
  { labels := observedLabels tg
    regime := observedRegime tg
    geometry := observedGeometry tg
    shapeFamily := observedShapeFamily tg }

def observedRowShape (tg : ObservedTarget) : List ObservedShapeCoord :=
  (observedGeometry tg).rowShape

def observedAtomCount (tg : ObservedTarget) : Nat :=
  (observedGeometry tg).atomCount

def observedShapeCount (tg : ObservedTarget) : Nat :=
  (observedGeometry tg).shapeCount

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
