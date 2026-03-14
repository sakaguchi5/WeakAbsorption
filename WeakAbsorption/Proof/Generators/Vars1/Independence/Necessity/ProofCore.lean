import WeakAbsorption.Proof.Generators.Kernel

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity
namespace ProofCore

inductive Pat : Nat → Type
  | var {n : Nat} : Fin n → Pat n
  | op  {n : Nat} : Pat n → Pat n → Pat n



namespace Pat

variable {α : Type}

def inst {n : Nat} (σ : Fin n → Term α) : Pat n → Term α
  | .var i  => σ i
  | .op p q => (inst σ p).op (inst σ q)

end Pat

/-- `t` is a root-instance of the pattern `p`. -/
def RootInstance {α : Type} {n : Nat} (p : Pat n) (t : Term α) : Prop :=
  ∃ σ : Fin n → Term α, Pat.inst σ p = t

/-- `t` is not a root-instance of the pattern `p`. -/
def NoRootInstance {α : Type} {n : Nat} (p : Pat n) (t : Term α) : Prop :=
  ∀ σ : Fin n → Term α, Pat.inst σ p ≠ t

/-- Any root-match of `p` to `t` forces the constraint `Φ`. -/
def RootMatchForces {n : Nat} (p : Pat n) (t : Term α)
    (Φ : (Fin n → Term α) → Prop) : Prop :=
  ∀ σ, Pat.inst σ p = t → Φ σ

theorem no_root_eq_of_no_instance₂
    {α : Type} {p : Pat 2} {target : Term α}
    (h : NoRootInstance p target) :
    ∀ a b : Term α,
      Pat.inst
        (fun (i : Fin 2) => -- ここで型を明示
          match i with
          | 0 => a
          | 1 => b)
        p ≠ target := by
  intro a b
  -- 以下の σ の定義でも同様に型を明示
  let σ : Fin 2 → Term α := fun (i : Fin 2) =>
    match i with
    | 0 => a
    | 1 => b
  exact h σ

theorem no_root_eq_of_no_instance₃
    {α : Type} {p : Pat 3} {target : Term α}
    (h : NoRootInstance p target) :
    ∀ a b c : Term α,
      Pat.inst
        (fun (i : Fin 3) => -- 型を明示してメタ変数を解消
          match i with
          | 0 => a
          | 1 => b
          | 2 => c)
        p ≠ target := by
  intro a b c
  let σ : Fin 3 → Term α := fun (i : Fin 3) =>
    match i with
    | 0 => a
    | 1 => b
    | 2 => c
  exact h σ


theorem noRootInstance_of_forces_and_refutes
    {n : Nat} {p : Pat n} {t : Term α} {Φ : (Fin n → Term α) → Prop}
    (hForces : RootMatchForces p t Φ)
    (hRefute : ∀ σ, Φ σ → Pat.inst σ p ≠ t) :
    NoRootInstance p t := by
  intro σ hEq
  exact hRefute σ (hForces σ hEq) hEq



end ProofCore
end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
