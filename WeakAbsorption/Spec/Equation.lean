import WeakAbsorption.Core.Syntax
import WeakAbsorption.Spec.Signatures

namespace WeakAbsorption
namespace Spec

open WeakAbsorption
open WeakAbsorption.Laws

/- C12代数を要求しない、生の二項演算での評価（探索用）。 -/
namespace Term
def evalOp {α A : Type} (op : A → A → A) (ρ : α → A) : Term α → A
  | .var a  => ρ a
  | .op t u => op (evalOp op ρ t) (evalOp op ρ u)
end Term

/-- 変数 `Fin vars` 上の項方程式。探索と証明の共通通貨。 -/
structure Eqn where
  name : String
  vars : Nat
  lhs  : Term (Fin vars)
  rhs  : Term (Fin vars)
  deriving Repr

/-- 任意の代入で成立（Prop版：証明用）。 -/
def Eqn.holdsOpP {A : Type} (E : Eqn) (op : A → A → A) : Prop :=
  ∀ ρ : Fin E.vars → A,
    Term.evalOp op ρ E.lhs = Term.evalOp op ρ E.rhs

/-- `Fin n` の全要素列挙（Mathlibなし）。 -/
def finList (n : Nat) : List (Fin n) :=
  match n with
  | 0 => []
  | n + 1 => (finList n).map (fun i => i.castSucc) ++ [Fin.last n]

/-- `Fin vars → Fin n` の全列挙（coreのみ） -/
def allAssign : (vars n : Nat) → List (Fin vars → Fin n)
  | 0,      _ => [fun i => i.elim0]
  | vars+1, n =>
      -- List.bind を明示的に呼び出し、flatMapとして機能させる
      (allAssign vars n).foldr (init := []) (fun ρ acc =>
        (finList n).map (fun a =>
          fun i => Fin.cases a ρ i
        ) ++ acc
      )

/-- List の全称チェック（Bool）。 -/
def listAll {α : Type} (xs : List α) (p : α → Bool) : Bool :=
  xs.foldl (fun acc x => acc && p x) true

/-- Fin n 上の op で Eqn が成り立つか（Bool版：探索用）。 -/
def Eqn.holdsOpB (E : Eqn) {n : Nat} : LawB n := fun op =>
  listAll (allAssign E.vars n) (fun ρ =>
    decide (Term.evalOp op ρ E.lhs = Term.evalOp op ρ E.rhs))

/- 代表的な法則を Eqn として用意（まずは C1/C2'/M2）。 -/

private def f2_0 : Fin 2 := ⟨0, by decide⟩
private def f2_1 : Fin 2 := ⟨1, by decide⟩

private def f3_0 : Fin 3 := ⟨0, by decide⟩
private def f3_1 : Fin 3 := ⟨1, by decide⟩
private def f3_2 : Fin 3 := ⟨2, by decide⟩

def eqnC1 : Eqn :=
  let x : Term (Fin 2) := Term.var f2_0
  let y : Term (Fin 2) := Term.var f2_1
  { name := "C1"
    vars := 2
    lhs  := Term.op (Term.op x y) y
    rhs  := Term.op x y }

def eqnC2p : Eqn :=
  let x : Term (Fin 3) := Term.var f3_0
  let y : Term (Fin 3) := Term.var f3_1
  let z : Term (Fin 3) := Term.var f3_2
  { name := "C2'"
    vars := 3
    lhs  := Term.op (Term.op (Term.op x y) z) (Term.op y z)
    rhs  := Term.op (Term.op x y) z }

def eqnM2 : Eqn :=
  let x : Term (Fin 3) := Term.var f3_0
  let y : Term (Fin 3) := Term.var f3_1
  let z : Term (Fin 3) := Term.var f3_2
  { name := "M2"
    vars := 3
    lhs  := Term.op (Term.op (Term.op x y) z) (Term.op y (Term.op z z))
    rhs  := Term.op (Term.op x y) z }

end Spec
end WeakAbsorption
