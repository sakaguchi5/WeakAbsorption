import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Proof.Generators.Vars1.Independence.Models.R3M4
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open Models.R3M4

abbrev V : Type := Fin 1

-- ----- witness terms (C2C1-shape instance) -----
def x : Term V := Term.var 0
def s : Term V := x.op x
def X : Term V := x.op s              -- x ⋆ (x⋆x)  == x ⋆ s
def PZ : Term V := X.op x             -- (x⋆(x⋆x)) ⋆ x
def vTerm : Term V := (X.op PZ).op x  -- (X ⋆ (X⋆x)) ⋆ x
def uTerm : Term V := vTerm.op PZ     -- ((X⋆(X⋆x))⋆x) ⋆ (X⋆x)

-- ----- Normality proofs (no search, purely structural) -----
private theorem x_normal : Normal (α := V) x := by
  intro u hu
  nomatch hu

private theorem not_C1_var (u : Term V) : ¬ IsC1Root (α := V) x u := by
  rintro ⟨w, hw⟩
  cases hw

private theorem not_C2_var (u : Term V) : ¬ IsC2pRoot (α := V) x u := by
  cases u <;> simp [IsC2pRoot, x]

private theorem s_normal : Normal (α := V) s := by
  apply (Normal_op_iff (α := V) x x).2
  refine ⟨x_normal, x_normal, ?_, ?_⟩
  · exact not_C1_var (u := x)
  · simp [IsC2pRoot, x]

private theorem X_normal : Normal (α := V) X := by
  apply (Normal_op_iff (α := V) x s).2
  refine ⟨x_normal, s_normal, ?_, ?_⟩
  · exact not_C1_var (u := s)
  · -- IsC2pRoot x s is impossible (var = op ...)
    dsimp [IsC2pRoot, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem not_C1_X_x : ¬ IsC1Root (α := V) X x := by
  rintro ⟨w, hw⟩
  -- X = w ⋆ x; but X = x ⋆ s, so right child mismatch
  dsimp [X, s, x] at hw
  injection hw with hL hR
  -- hR : (var 0 ⋆ var 0) = var 0
  cases hR

private theorem PZ_normal : Normal (α := V) PZ := by
  apply (Normal_op_iff (α := V) X x).2
  refine ⟨X_normal, x_normal, ?_, ?_⟩
  · exact not_C1_X_x
  · simp [IsC2pRoot, x]  -- right is var → false

private theorem not_C1_X_PZ : ¬ IsC1Root (α := V) X PZ := by
  rintro ⟨w, hw⟩
  dsimp [X, PZ, s, x] at hw
  injection hw with hL hR
  -- hR : (var 0 ⋆ var 0) = ((var 0 ⋆ (var 0 ⋆ var 0)) ⋆ var 0)
  cases hR

private theorem not_C2_X_PZ : ¬ IsC2pRoot (α := V) X PZ := by
  -- PZ = (X ⋆ x) so IsC2pRoot X PZ would force X = ((w⋆X)⋆x), impossible
  dsimp [IsC2pRoot, PZ, X, s, x]
  rintro ⟨w, hw⟩
  -- hw : x⋆(x⋆x) = ((w⋆(x⋆(x⋆x)))⋆x)
  injection hw with h1 h2
  -- right child mismatch: (x⋆x) = x
  cases h2

private theorem XPZ_normal : Normal (α := V) (X.op PZ) := by
  apply (Normal_op_iff (α := V) X PZ).2
  refine ⟨X_normal, PZ_normal, ?_, ?_⟩
  · exact not_C1_X_PZ
  · exact not_C2_X_PZ

private theorem not_C1_XPZ_x : ¬ IsC1Root (α := V) (X.op PZ) x := by
  rintro ⟨w, hw⟩
  dsimp [X, PZ, s, x] at hw
  injection hw with hL hR
  -- hR : PZ = x
  cases hR

private theorem v_normal : Normal (α := V) vTerm := by
  apply (Normal_op_iff (α := V) (X.op PZ) x).2
  refine ⟨XPZ_normal, x_normal, ?_, ?_⟩
  · exact not_C1_XPZ_x
  · simp [IsC2pRoot, x]  -- right var

private theorem not_C1_v_PZ : ¬ IsC1Root (α := V) vTerm PZ := by
  rintro ⟨w, hw⟩
  -- vTerm right child is x, cannot be PZ
  dsimp [vTerm, PZ, X, s, x] at hw
  injection hw with hL hR
  -- hR : x = PZ
  cases hR

private theorem not_C2_v_PZ : ¬ IsC2pRoot (α := V) vTerm PZ := by
  dsimp [IsC2pRoot, PZ, vTerm, X, s, x]
  rintro ⟨w, hw⟩
  injection hw with h1 h2
  -- left child mismatch forces PZ = X
  cases h1

private theorem u_normal : Normal (α := V) uTerm := by
  apply (Normal_op_iff (α := V) vTerm PZ).2
  refine ⟨v_normal, PZ_normal, ?_, ?_⟩
  · exact not_C1_v_PZ
  · exact not_C2_v_PZ

def nfV : NormalForm V := ⟨vTerm, v_normal⟩
def nfU : NormalForm V := ⟨uTerm, u_normal⟩

theorem nfU_ne_nfV : nfU.1 ≠ nfV.1 := by
  intro h
  -- uTerm is an op with right child PZ; vTerm is op with right child x
  dsimp [nfU, nfV, uTerm, vTerm, PZ, X, s, x] at h
  injection h with h1 h2
  -- h2 : PZ = x
  cases h2

-- ----- NFRel witness: C2C1-derived RedEq -----
theorem nfRel_nfU_nfV : NFRel (α := V) nfU nfV := by
  -- NFRel is RedEq on underlying terms
  dsimp [NFRel, nfU, nfV, uTerm, vTerm, PZ, X, s, x]
  -- instantiate RedEq_C2C1_right with x0:=X, p:=X, z:=x, and C=hole
  simpa using (RedEq_C2C1_right (α := V) (x := X) (p := X) (z := x))

-- ----- Not derivable from R3 by model evaluation -----
abbrev R3set : RuleSet := Vars1.R3

def ρ : V → M4 := fun _ => .m3

theorem eval_nfV : eval (α := V) ρ nfV.1 = .m1 := by
  -- computed value under the operation table
  simp [eval, Models.R3M4.mul, ρ, nfV, vTerm, PZ, X, s, x]

theorem eval_nfU : eval (α := V) ρ nfU.1 = .m0 := by
  simp [eval, Models.R3M4.mul, ρ, nfU, uTerm, vTerm, PZ, X, s, x]

theorem not_NFEqR_R3_nfU_nfV : ¬ NFEqR (α := V) R3set nfU nfV := by
  intro h
  have hev :=
    eval_eq_of_NFEqR_R3 (α := V) (ρ := ρ) (x := nfU) (y := nfV) h
  have hu : eval (α := V) ρ nfU.1 = .m0 := eval_nfU
  have hv : eval (α := V) ρ nfV.1 = .m1 := eval_nfV
  have h_eq : (M4.m0 : M4) = M4.m1 := by
    simp [hu, hv] at hev
  have h_ne : ¬ ((M4.m0 : M4) = M4.m1) := by decide
  exact h_ne h_eq

/-- (i) result: R3 is incomplete; C2C1 witness survives. -/
theorem R3_incomplete_C2C1 :
  ∃ x y : NormalForm V,
    x.1 ≠ y.1 ∧ NFRel (α := V) x y ∧ ¬ NFEqR (α := V) R3set x y := by
  refine ⟨nfU, nfV, ?_, nfRel_nfU_nfV, not_NFEqR_R3_nfU_nfV⟩
  exact nfU_ne_nfV

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
