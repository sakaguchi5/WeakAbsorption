import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Targets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness

/--
Main targets for which we track an explicit `plug_eq_*_lhs_cases` decomposition.
This is intentionally smaller than `RootTarget`: it only contains targets whose
plug decomposition has already been made explicit in `DoubleSq_R4.lean`.
-/
inductive PlugMainTarget where
  | xAStablePred
  | uStablePred
  | uHolePred
  | uDecorHolePred
  | m
  | uDecorRightPred
  | xASqRightPred
  | uSqLiftRightPred
  | xADecorRightPred
  | uDecorLiftRightPred
  | xASqAPred
  | uSqLiftAPred
  | xADecorLeftPred
  | uDecorLiftLeftPred
deriving DecidableEq, Repr

/--
Named subterms that recur in plug decompositions.
These are the pieces we expect left/right branches to recurse into.
-/
inductive PlugSubterm where
  | x
  | s
  | v
  | A
  | xA
  | Ax
  | u
  | sA
  | sv
  | ssv
  | svs
  | AA
  | xAStablePred
  | xASqRightPred
  | xADecorRightPred
  | xASqAPred
  | xADecorLeftPred
deriving DecidableEq, Repr


/-- Reusable rhs decomposition families tracked as first-class plug targets. -/
inductive PlugRhsTarget where
  | sA
  | sv
  | ssv
  | svs
  | AA
deriving DecidableEq, Repr

/-- Underlying named subterm attached to each rhs plug target. -/
def plugRhsTargetSubterm : PlugRhsTarget -> PlugSubterm
  | .sA  => .sA
  | .sv  => .sv
  | .ssv => .ssv
  | .svs => .svs
  | .AA  => .AA

/-- Concrete term attached to each named recurring plug subterm. -/
def plugSubtermTerm : PlugSubterm -> Term V
  | .x                => x
  | .s                => s
  | .v                => vTerm
  | .A                => A
  | .xA               => xATerm
  | .Ax               => A.op x
  | .u                => uTerm
  | .sA               => s.op A
  | .sv               => s.op vTerm
  | .ssv              => s.op (s.op vTerm)
  | .svs              => (s.op vTerm).op s
  | .AA               => A.op A
  | .xAStablePred     => xAStablePredTerm
  | .xASqRightPred    => xASqRightSPredTerm
  | .xADecorRightPred => xADecorRightSPredTerm
  | .xASqAPred        => xASqAPredTerm
  | .xADecorLeftPred  => xADecorLeftSPredTerm

/-- Concrete term attached to each rhs plug target. -/
def plugRhsTargetTerm (tg : PlugRhsTarget) : Term V :=
  plugSubtermTerm (plugRhsTargetSubterm tg)

/-- Concrete term attached to each main plug target. -/
def plugMainTargetTerm : PlugMainTarget -> Term V
  | .xAStablePred      => xAStablePredTerm
  | .uStablePred       => uStablePredTerm
  | .uHolePred         => uHolePredTerm
  | .uDecorHolePred    => uDecorHolePredTerm
  | .m                 => mTerm
  | .uDecorRightPred   => uDecorRightPredTerm
  | .xASqRightPred     => xASqRightSPredTerm
  | .uSqLiftRightPred  => uSqLiftRightSPredTerm
  | .xADecorRightPred  => xADecorRightSPredTerm
  | .uDecorLiftRightPred => uDecorLiftRightSPredTerm
  | .xASqAPred         => xASqAPredTerm
  | .uSqLiftAPred      => uSqLiftAPredTerm
  | .xADecorLeftPred   => xADecorLeftSPredTerm
  | .uDecorLiftLeftPred => uDecorLiftLeftSPredTerm



/-- Metadata for a binary `plug_eq_*_lhs_cases` decomposition. -/
structure PlugLhsRow where
  left  : PlugSubterm
  right : PlugSubterm

/-- Metadata for a recurring rhs decomposition family. -/
structure PlugRhsRow where
  left  : PlugSubterm
  right : PlugSubterm

/-- The explicit lhs decomposition row for each registered main plug target. -/
def plugLhsRow : PlugMainTarget -> PlugLhsRow
  | .xAStablePred =>
      { left := .x, right := .Ax }
  | .uStablePred =>
      { left := .xAStablePred, right := .s }
  | .uHolePred =>
      { left := .u, right := .A }
  | .uDecorHolePred =>
      { left := .u, right := .sA }
  | .m =>
      { left := .v, right := .sv }
  | .uDecorRightPred =>
      { left := .xA, right := .sv }
  | .xASqRightPred =>
      { left := .x, right := .sA }
  | .uSqLiftRightPred =>
      { left := .xASqRightPred, right := .s }
  | .xADecorRightPred =>
      { left := .x, right := .ssv }
  | .uDecorLiftRightPred =>
      { left := .xADecorRightPred, right := .s }
  | .xASqAPred =>
      { left := .x, right := .AA }
  | .uSqLiftAPred =>
      { left := .xASqAPred, right := .s }
  | .xADecorLeftPred =>
      { left := .x, right := .svs }
  | .uDecorLiftLeftPred =>
      { left := .xADecorLeftPred, right := .s }

/-- Reusable rhs decomposition families currently explicit in `DoubleSq_R4.lean`. -/
def plugRhsRow : PlugSubterm -> Option PlugRhsRow
  | .sA  => some { left := .s,  right := .A }
  | .sv  => some { left := .s,  right := .v }
  | .ssv => some { left := .s,  right := .sv }
  | .svs => some { left := .sv, right := .s }
  | .AA  => some { left := .A,  right := .A }
  | _    => none


/-- Row-level registry view for a main plug target. -/
structure PlugLhsRowView where
  target : PlugMainTarget
  term   : Term V
  row    : PlugLhsRow

/-- Full lhs plug-decomposition registry entry for a main plug target. -/
def plugLhsRowView (tg : PlugMainTarget) : PlugLhsRowView :=
  { target := tg
    term := plugMainTargetTerm tg
    row := plugLhsRow tg }

@[simp] theorem plugLhsRowView_term (tg : PlugMainTarget) :
    (plugLhsRowView tg).term = plugMainTargetTerm tg := rfl

@[simp] theorem plugLhsRowView_row (tg : PlugMainTarget) :
    (plugLhsRowView tg).row = plugLhsRow tg := rfl


/-- Row-level registry view for a reusable rhs plug target. -/
structure PlugRhsRowView where
  target : PlugRhsTarget
  term   : Term V
  row    : PlugRhsRow

/-- Full rhs plug-decomposition registry entry for a reusable rhs plug target. -/
def plugRhsRowView (tg : PlugRhsTarget) : PlugRhsRowView :=
  match tg with
  | .sA  => { target := tg, term := plugRhsTargetTerm tg, row := { left := .s,  right := .A } }
  | .sv  => { target := tg, term := plugRhsTargetTerm tg, row := { left := .s,  right := .v } }
  | .ssv => { target := tg, term := plugRhsTargetTerm tg, row := { left := .s,  right := .sv } }
  | .svs => { target := tg, term := plugRhsTargetTerm tg, row := { left := .sv, right := .s } }
  | .AA  => { target := tg, term := plugRhsTargetTerm tg, row := { left := .A,  right := .A } }

@[simp] theorem plugRhsRowView_term (tg : PlugRhsTarget) :
    (plugRhsRowView tg).term = plugRhsTargetTerm tg := by cases tg <;> rfl

@[simp] theorem plugRhsRowView_row (tg : PlugRhsTarget) :
    (plugRhsRowView tg).row = (match tg with
      | .sA  => { left := .s,  right := .A }
      | .sv  => { left := .s,  right := .v }
      | .ssv => { left := .s,  right := .sv }
      | .svs => { left := .sv, right := .s }
      | .AA  => { left := .A,  right := .A }) := by
  cases tg <;> rfl

/-- RHS plug targets currently registered. -/
def plugRhsTargets : List PlugRhsTarget :=
  [ .sA, .sv, .ssv, .svs, .AA ]

/-- Main plug targets currently registered. -/
def plugMainTargets : List PlugMainTarget :=
  [ .xAStablePred, .uStablePred, .uHolePred, .uDecorHolePred,
    .m, .uDecorRightPred,
    .xASqRightPred, .uSqLiftRightPred,
    .xADecorRightPred, .uDecorLiftRightPred,
    .xASqAPred, .uSqLiftAPred,
    .xADecorLeftPred, .uDecorLiftLeftPred ]

/-- RHS decomposition families currently registered. -/
def plugRhsSubterms : List PlugSubterm :=
  [ .sA, .sv, .ssv, .svs, .AA ]

/-- Whether a subterm has an explicit reusable rhs decomposition row. -/
def hasPlugRhsRow (st : PlugSubterm) : Bool :=
  match plugRhsRow st with
  | some _ => true
  | none => false

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
