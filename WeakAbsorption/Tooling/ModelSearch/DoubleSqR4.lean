import WeakAbsorption.Tooling.ModelSearch.CounterexampleSearch

namespace WeakAbsorption
namespace ModelSearch

open WeakAbsorption.Spec
open WeakAbsorption.Laws

/-- R4 = SqAbsorb + SqStable + Decor + C2C1 (as identities) -/
def holdsR4 {n : Nat} (op : BinOp n) : Bool :=
  decide (∀ a b p z : Fin n,
    -- SqAbsorb: (a*b)*(b*b) = a*b
    op (op a b) (op b b) = op a b ∧
    -- SqStable: ((a*b)*(b*b))*b = (a*b)*(b*b)
    op (op (op a b) (op b b)) b = op (op a b) (op b b) ∧
    -- Decor: (a*b)*(b*(b*b)) = a*b
    op (op a b) (op b (op b b)) = op a b ∧
    -- C2C1: ((a*(p*z))*z)*(p*z) = (a*(p*z))*z
    op (op (op a (op p z)) z) (op p z) = op (op a (op p z)) z)

/-- DoubleSq witness under a fixed valuation x := k.
    s = x*x, A = s*s, u = (x*A)*s, v = x*s. -/
def doubleSqWitnessEq {n : Nat} (op : BinOp n) (k : Fin n) : Bool :=
  let x := k
  let s := op x x
  let A := op s s
  let u := op (op x A) s
  let v := op x s
  decide (u = v)

/-- Law: if R4 holds then DoubleSq witness must hold (for chosen k). -/
def law_DoubleSqR4 {n : Nat} (k : Fin n) : LawB n :=
  fun op => if holdsR4 op then doubleSqWitnessEq op k else true

/-- Search for a C1+C2' model that satisfies R4 but breaks the DoubleSq witness. -/
def findCounterexample_DoubleSqR4 (n : Nat) (k : Fin n) : Option (BinOp n) :=
  findCounterexample (n := n) (law_DoubleSqR4 (n := n) k)


end ModelSearch
end WeakAbsorption
