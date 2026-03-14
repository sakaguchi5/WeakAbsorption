import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore
import WeakAbsorption.Proof.Generators.Vars1.Independence.Witness.DoubleSq

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness



/-- `((a⋆b)⋆(b⋆b))` -/
def sqAbsorbPat : Pat 2 :=
  Pat.op
    (Pat.op (Pat.var 0) (Pat.var 1))
    (Pat.op (Pat.var 1) (Pat.var 1))

/-- `(((a⋆b)⋆(b⋆b))⋆b)` -/
def sqStablePat : Pat 2 :=
  Pat.op
    (Pat.op
      (Pat.op (Pat.var 0) (Pat.var 1))
      (Pat.op (Pat.var 1) (Pat.var 1)))
    (Pat.var 1)

/-- `((a⋆b)⋆(b⋆(b⋆b)))` -/
def decorPat : Pat 2 :=
  Pat.op
    (Pat.op (Pat.var 0) (Pat.var 1))
    (Pat.op (Pat.var 1)
      (Pat.op (Pat.var 1) (Pat.var 1)))

/-- `(((x0⋆(p⋆z0))⋆z0)⋆(p⋆z0))` -/
def c2c1Pat : Pat 3 :=
  Pat.op
    (Pat.op
      (Pat.op
        (Pat.var 0)
        (Pat.op (Pat.var 1) (Pat.var 2)))
      (Pat.var 2))
    (Pat.op (Pat.var 1) (Pat.var 2))

theorem no_sqAbsorb_root_eq_of_no_instance
    {α : Type} {target : Term α}
    (h : NoRootInstance sqAbsorbPat target) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target := by
  intro t u
  simpa [sqAbsorbPat, Pat.inst] using
    (ProofCore.no_root_eq_of_no_instance₂ (p := sqAbsorbPat) (target := target) h t u)

theorem no_sqStable_root_eq_of_no_instance
    {α : Type} {target : Term α}
    (h : NoRootInstance sqStablePat target) :
    ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ target := by
  intro t u
  simpa [sqStablePat, Pat.inst] using
    (ProofCore.no_root_eq_of_no_instance₂ (p := sqStablePat) (target := target) h t u)

theorem no_decor_root_eq_of_no_instance
    {α : Type} {target : Term α}
    (h : NoRootInstance decorPat target) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target := by
  intro t u
  simpa [decorPat, Pat.inst] using
    (ProofCore.no_root_eq_of_no_instance₂ (p := decorPat) (target := target) h t u)

theorem no_c2c1_root_eq_of_no_instance
    {α : Type} {target : Term α}
    (h : NoRootInstance c2c1Pat target) :
    ∀ x0 p z0 : Term α, (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ target := by
  intro x0 p z0
  simpa [c2c1Pat, Pat.inst] using
    (ProofCore.no_root_eq_of_no_instance₃ (p := c2c1Pat) (target := target) h x0 p z0)
theorem no_sqAbsorb_root_var_left_target
    {α : Type} (a : α) (q : Term α) :
    NoRootInstance sqAbsorbPat ((Term.var a).op q) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  injection hEq with hL hR
  cases hL

theorem no_sqStable_root_var_left_target
    {α : Type} (a : α) (q : Term α) :
    NoRootInstance sqStablePat ((Term.var a).op q) := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst] at hEq
  injection hEq with hL hR
  cases hL

theorem no_decor_root_var_left_target
    {α : Type} (a : α) (q : Term α) :
    NoRootInstance decorPat ((Term.var a).op q) := by
  intro σ hEq
  dsimp [decorPat, Pat.inst] at hEq
  injection hEq with hL hR
  cases hL

theorem no_c2c1_root_var_left_target
    {α : Type} (a : α) (q : Term α) :
    NoRootInstance c2c1Pat ((Term.var a).op q) := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst] at hEq
  injection hEq with hL hR
  cases hL




end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
