import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Targets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness

/-- The four root rules that matter for the R4 root-behavior table. -/
inductive RootRule where
  | sqAbsorb
  | sqStable
  | decor
  | c2c1
deriving DecidableEq, Repr

/-- Targets whose root behavior is tracked explicitly. -/
inductive RootTarget where
  | xASqAPred
  | xASqRightPred
  | xAStablePred
  | xADecorAPred
  | xADecorLeftPred
  | xADecorRightPred
  | uSqLiftAPred
  | uSqLiftRightPred
  | uDecorLiftLeftPred
  | uDecorLiftRightPred
  | uDecorRightPred
  | uStablePred
  | uHolePred
  | uDecorHolePred
deriving DecidableEq, Repr

/-- Coarse root outcome: either impossible at root, or genuinely productive. -/
inductive RootOutcome where
  | noRoot
  | productive
deriving DecidableEq, Repr

/--
The current best explanation of a `noRoot` cell.
This is metadata first: it records the mechanism we believe is minimal.
Some cells may later be improved by audit, so `pendingAudit` remains available.
-/
inductive NoRootMechanism where
  | varLeft
  | globalNomatch
  | leftShell1
  | rightShell1
  | projForceLeft
  | projForceRight
  | pendingAudit
deriving DecidableEq, Repr


/-- Row-level shape: either all four root cells are `noRoot`, or some are genuinely productive. -/
inductive RootRowKind where
  | noRootRow
  | mixedRow
deriving DecidableEq, Repr

/-- The concrete term attached to each registered target. -/
def rootTargetTerm : RootTarget -> Term V
  | .xASqAPred        => xASqAPredTerm
  | .xASqRightPred    => xASqRightSPredTerm
  | .xAStablePred     => xAStablePredTerm
  | .xADecorAPred     => xADecorAPredTerm
  | .xADecorLeftPred  => xADecorLeftSPredTerm
  | .xADecorRightPred => xADecorRightSPredTerm
  | .uSqLiftAPred     => uSqLiftAPredTerm
  | .uSqLiftRightPred => uSqLiftRightSPredTerm
  | .uDecorLiftLeftPred  => uDecorLiftLeftSPredTerm
  | .uDecorLiftRightPred => uDecorLiftRightSPredTerm
  | .uDecorRightPred  => uDecorRightPredTerm
  | .uStablePred      => uStablePredTerm
  | .uHolePred        => uHolePredTerm
  | .uDecorHolePred   => uDecorHolePredTerm

structure RootOutcomeRow where
  sqAbsorb : RootOutcome
  sqStable : RootOutcome
  decor    : RootOutcome
  c2c1     : RootOutcome

def rootOutcomeRow : RootTarget -> RootOutcomeRow
  | .xASqAPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .xASqRightPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .xAStablePred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .xADecorAPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .xADecorLeftPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .xADecorRightPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uSqLiftAPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uSqLiftRightPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uDecorLiftLeftPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uDecorLiftRightPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uDecorRightPred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uStablePred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .noRoot, c2c1 := .noRoot }
  | .uHolePred =>
      { sqAbsorb := .productive, sqStable := .noRoot, decor := .noRoot, c2c1 := .productive }
  | .uDecorHolePred =>
      { sqAbsorb := .noRoot, sqStable := .noRoot, decor := .productive, c2c1 := .noRoot }

structure NoRootMechanismRow where
  sqAbsorb : Option NoRootMechanism
  sqStable : Option NoRootMechanism
  decor    : Option NoRootMechanism
  c2c1     : Option NoRootMechanism

/-- Registry-level row view for a target. -/
structure RootRowView where
  kind       : RootRowKind
  outcomes   : RootOutcomeRow
  mechanisms : NoRootMechanismRow

def noRootMechanismRow : RootTarget -> NoRootMechanismRow
  | .xASqAPred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .xASqRightPred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .xAStablePred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .xADecorAPred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .xADecorLeftPred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .xADecorRightPred =>
      { sqAbsorb := some .varLeft, sqStable := some .varLeft, decor := some .varLeft, c2c1 := some .varLeft }
  | .uSqLiftAPred =>
      { sqAbsorb := some .projForceLeft, sqStable := some .globalNomatch, decor := some .rightShell1, c2c1 := some .leftShell1 }
  | .uSqLiftRightPred =>
      { sqAbsorb := some .projForceLeft, sqStable := some .globalNomatch, decor := some .projForceRight, c2c1 := some .globalNomatch }
  | .uDecorLiftLeftPred =>
      { sqAbsorb := some .projForceLeft, sqStable := some .globalNomatch, decor := some .projForceRight, c2c1 := some .leftShell1 }
  | .uDecorLiftRightPred =>
      { sqAbsorb := some .projForceLeft, sqStable := some .globalNomatch, decor := some .rightShell1, c2c1 := some .leftShell1 }
  | .uDecorRightPred =>
      { sqAbsorb := some .projForceRight, sqStable := some .globalNomatch, decor := some .projForceRight, c2c1 := some .globalNomatch }
  | .uStablePred =>
      { sqAbsorb := some .globalNomatch, sqStable := some .globalNomatch, decor := some .rightShell1, c2c1 := some .globalNomatch }
  | .uHolePred =>
      { sqAbsorb := none, sqStable := some .globalNomatch, decor := some .globalNomatch, c2c1 := none }
  | .uDecorHolePred =>
      { sqAbsorb := some .globalNomatch, sqStable := some .globalNomatch, decor := none, c2c1 := some .globalNomatch }

def rootOutcome (r : RootRule) (tg : RootTarget) : RootOutcome :=
  match r, rootOutcomeRow tg with
  | .sqAbsorb, row => row.sqAbsorb
  | .sqStable, row => row.sqStable
  | .decor,    row => row.decor
  | .c2c1,     row => row.c2c1

def noRootMechanism? (r : RootRule) (tg : RootTarget) : Option NoRootMechanism :=
  match r, noRootMechanismRow tg with
  | .sqAbsorb, row => row.sqAbsorb
  | .sqStable, row => row.sqStable
  | .decor,    row => row.decor
  | .c2c1,     row => row.c2c1




def rootRowKind : RootTarget -> RootRowKind
  | .xASqAPred        => .noRootRow
  | .xASqRightPred    => .noRootRow
  | .xAStablePred     => .noRootRow
  | .xADecorAPred     => .noRootRow
  | .xADecorLeftPred  => .noRootRow
  | .xADecorRightPred => .noRootRow
  | .uSqLiftAPred     => .noRootRow
  | .uSqLiftRightPred => .noRootRow
  | .uDecorLiftLeftPred  => .noRootRow
  | .uDecorLiftRightPred => .noRootRow
  | .uDecorRightPred  => .noRootRow
  | .uStablePred      => .noRootRow
  | .uHolePred        => .mixedRow
  | .uDecorHolePred   => .mixedRow

/-- Full row-level registry entry for a target. -/
def rootRowView (tg : RootTarget) : RootRowView :=
  { kind := rootRowKind tg
    outcomes := rootOutcomeRow tg
    mechanisms := noRootMechanismRow tg }

/-- Targets whose four root cells are all no-root. -/
def noRootRowTargets : List RootTarget :=
  [ .xASqAPred, .xASqRightPred, .xAStablePred, .xADecorAPred,
    .xADecorLeftPred, .xADecorRightPred,
    .uSqLiftAPred, .uSqLiftRightPred,
    .uDecorLiftLeftPred, .uDecorLiftRightPred,
    .uDecorRightPred, .uStablePred ]

/-- Targets whose row mixes no-root cells and productive cells. -/
def mixedRowTargets : List RootTarget :=
  [ .uHolePred, .uDecorHolePred ]

/-- Boolean view of whether a target belongs to a pure no-root row. -/
def isNoRootRowTarget (tg : RootTarget) : Bool :=
  match rootRowKind tg with
  | .noRootRow => true
  | .mixedRow  => false

/-- Boolean view of whether a target belongs to a mixed/productive row. -/
def isMixedRowTarget (tg : RootTarget) : Bool :=
  match rootRowKind tg with
  | .noRootRow => false
  | .mixedRow  => true

/-- Row targets grouped by their row-level shape. -/
def rowTargetsOfKind (k : RootRowKind) : List RootTarget :=
  match k with
  | .noRootRow => noRootRowTargets
  | .mixedRow  => mixedRowTargets

/-- Cells whose coarse root outcome is fixed, but whose *minimal* no-root mechanism still needs audit. -/
def pendingAuditCells : List (RootRule × RootTarget) :=
  []

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
