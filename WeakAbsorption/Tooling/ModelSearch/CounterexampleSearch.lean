import WeakAbsorption.Tooling.ModelSearch.Core
import WeakAbsorption.Spec.Signatures
import WeakAbsorption.Spec.Equation

namespace WeakAbsorption
namespace ModelSearch

open WeakAbsorption.Laws

open WeakAbsorption.Spec

/-- 完成状態 `sol` が law の反例になっているか -/
def isCounterexample {n : Nat} (law : LawB n) (idem : Array (IMap n)) (sol : State n) : Bool :=
  let op := opOf idem sol
  !(law op)

/-- C1+C2' を満たすモデルを探索しつつ、law を壊す反例を1つ探す（汎用版） -/
partial def searchCounterexample {n : Nat} (law : LawB n) (idem : Array (IMap n)) (st : State n)
  : Option (State n) := Id.run do
  match propagate idem st with
  | none => return none
  | some st' =>
      match pickVar st' with
      | none =>
          if isCounterexample law idem st' then
            return some st'
          else
            return none
      | some y =>
          let opts := st'.cands[y.1]!
          for i in opts do
            match searchCounterexample law idem (st'.setAssign y i) with
            | some sol => return some sol
            | none => ()
          return none

/-- C1+C2' を満たし、かつ law を壊すモデルを1つ探す（汎用版） -/
def findCounterexample {n : Nat} (law : LawB n) : Option (BinOp n) :=
  let idem := (idemMaps n).toArray
  match searchCounterexample law idem (State.init idem) with
  | some sol => some (opOf idem sol)
  | none => none

/-- 既存M2探索との互換ラッパ（段階移行用） -/
def findCounterexampleM2' (n : Nat) : Option (BinOp n) :=
  findCounterexample (n := n) holdsM2B

/-- Eqn を LawB に変換して反例探索する薄いラッパ -/
def findCounterexampleEqn {n : Nat} (E : Eqn) : Option (BinOp n) :=
  findCounterexample (n := n) (Eqn.holdsOpB (n := n) E)

end ModelSearch
end WeakAbsorption
