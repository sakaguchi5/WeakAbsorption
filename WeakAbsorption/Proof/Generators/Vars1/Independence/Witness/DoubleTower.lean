import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
namespace DoubleTower
open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA




abbrev V : Type := Fin 1

def x : Term V := .var 0

/--
Repeated squaring tower over the single variable.

tower 0 = x
tower 1 = x ⋆ x
tower 2 = (x ⋆ x) ⋆ (x ⋆ x)
tower 3 = tower 2 ⋆ tower 2
...
-/
def tower : Nat → Term V
  | 0 => x
  | n + 1 => (tower n).op (tower n)

@[simp] theorem tower_zero : tower 0 = x := rfl
@[simp] theorem tower_succ (n : Nat) : tower (n + 1) = (tower n).op (tower n) := rfl

/-- No term can equal itself with one extra left layer: t ≠ (t ⋆ u). -/
private theorem no_eq_op_left_self {α : Type} (t u : Term α) :
    t ≠ Term.op t u := by
  induction t generalizing u with
  | var a =>
      intro h
      cases h
  | op l r ihl ihr =>
      intro h
      injection h with hL hR
      exact ihl r hL

/-- No term can equal itself with one extra right layer: t ≠ (u ⋆ t). -/
private theorem no_eq_op_right_self {α : Type} (t u : Term α) :
    t ≠ Term.op u t := by
  induction t generalizing u with
  | var a =>
      intro h
      cases h
  | op l r ihl ihr =>
      intro h
      injection h with hL hR
      exact ihr l hR

/-- Generic exclusion of a C1-root at `(t ⋆ t)`. -/
private theorem not_IsC1Root_self {α : Type} (t : Term α) :
    ¬ IsC1Root (α := α) t t := by
  rintro ⟨u, hu⟩
  exact no_eq_op_right_self t u hu

/-- Generic exclusion of a C2'-root at `(t ⋆ t)`. -/
private theorem not_IsC2pRoot_self {α : Type} (t : Term α) :
    ¬ IsC2pRoot (α := α) t t := by
  cases t with
  | var a =>
      simp [IsC2pRoot]
  | op y z =>
      dsimp [IsC2pRoot]
      rintro ⟨u, hu⟩
      injection hu with h1 h2
      exact no_eq_op_right_self y u h1

private theorem x_normal : Normal (α := V) x := by
  intro u hu
  nomatch hu

/-- Every repeated-squaring tower is normal for the base rewrite system. -/
private theorem tower_normal : ∀ n : Nat, Normal (α := V) (tower n)
  | 0 => x_normal
  | n + 1 =>
      (Normal_op_iff (α := V) (tower n) (tower n)).2 <|
        ⟨tower_normal n, tower_normal n,
         not_IsC1Root_self (tower n),
         not_IsC2pRoot_self (tower n)⟩

/-- Successive tower levels are distinct. -/
private theorem tower_succ_ne (n : Nat) :
    tower (n + 1) ≠ tower n := by
  intro h
  exact no_eq_op_left_self (tower n) (tower n) h.symm

/--
Right-hand normal form of the nth tower-collapse witness:
rhs 0 = x ⋆ (x ⋆ x)
rhs 1 = x ⋆ tower 2
rhs 2 = x ⋆ tower 3
...
-/
def towerRhsTerm (n : Nat) : Term V :=
  x.op (tower (n + 1))

/--
Left-hand normal form of the nth tower-collapse witness:
lhs 0 = (x ⋆ tower 2) ⋆ tower 1
lhs 1 = (x ⋆ tower 3) ⋆ tower 2
lhs 2 = (x ⋆ tower 4) ⋆ tower 3
...
-/
def towerLhsTerm (n : Nat) : Term V :=
  (x.op (tower (n + 2))).op (tower (n + 1))

private theorem towerRhs_normal (n : Nat) :
    Normal (α := V) (towerRhsTerm n) := by
  apply (Normal_op_iff (α := V) x (tower (n + 1))).2
  refine ⟨x_normal, tower_normal (n + 1), ?_, ?_⟩
  · rintro ⟨u, hu⟩
    cases hu
  · cases tower (n + 1) <;> simp [IsC2pRoot, x]

private theorem x_tower_normal (n : Nat) :
    Normal (α := V) (x.op (tower (n + 2))) := by
  apply (Normal_op_iff (α := V) x (tower (n + 2))).2
  refine ⟨x_normal, tower_normal (n + 2), ?_, ?_⟩
  · rintro ⟨u, hu⟩
    cases hu
  · cases tower (n + 2) <;> simp [IsC2pRoot, x]

private theorem towerLhs_normal (n : Nat) :
    Normal (α := V) (towerLhsTerm n) := by
  apply (Normal_op_iff (α := V) (x.op (tower (n + 2))) (tower (n + 1))).2
  refine ⟨x_tower_normal n, tower_normal (n + 1), ?_, ?_⟩
  · rintro ⟨u, hu⟩
    injection hu with h1 h2
    exact tower_succ_ne (n + 1) h2
  · change ¬ ∃ u : Term V,
        x.op (tower (n + 2)) = Term.op (Term.op u (tower n)) (tower n)
    rintro ⟨u, hu⟩
    injection hu with h1 h2
    cases h1

def nfTowerRhs (n : Nat) : NormalForm V :=
  ⟨towerRhsTerm n, towerRhs_normal n⟩

def nfTowerLhs (n : Nat) : NormalForm V :=
  ⟨towerLhsTerm n, towerLhs_normal n⟩

theorem towerLhs_ne_towerRhs (n : Nat) :
    (nfTowerLhs n).1 ≠ (nfTowerRhs n).1 := by  -- ここに := を追加
  intro h
  dsimp [nfTowerLhs, nfTowerRhs, towerLhsTerm, towerRhsTerm, x] at h
  -- h : (x.op (tower (n + 2))).op (tower (n + 1)) = x.op (tower (n + 1))
  injection h with h1 h2
  -- h1 : x.op (tower (n + 2)) = x
  cases h1

/--
Generalized DoubleSq witness family.

At level n, the built-in DoubleSq-derived NF step identifies
  (x ⋆ tower (n+2)) ⋆ tower (n+1)
with
  x ⋆ tower (n+1).

This is the tower analogue of the original `DoubleSq.lean` witness.
-/
theorem tower_nfRel (n : Nat) :
    NFRel (α := V) (nfTowerLhs n) (nfTowerRhs n) := by
  apply NFDoubleSqStepCtx_imp_NFRel (α := V)
  refine ⟨Ctx.hole, x, tower n, ?_, ?_⟩ <;> rfl

/-- The original DoubleSq witness is exactly the n = 0 tower witness. -/
theorem tower_nfRel_zero :
    NFRel (α := V) (nfTowerLhs 0) (nfTowerRhs 0) := by
  simpa using tower_nfRel 0

end WeakAbsorption.Proof.Generators.Vars1.Independence.Witness.DoubleTower
