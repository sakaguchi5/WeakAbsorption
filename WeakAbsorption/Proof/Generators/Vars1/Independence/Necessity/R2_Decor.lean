import WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step16
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Proof.Generators.Vars1.Independence.Models.R2M3
import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open Models.R2M3

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step16
open WeakAbsorption.Proof.Generators.Vars1.Complete
open WeakAbsorption.Proof.Generators.Vars1.Independence

abbrev R2 : RuleSet := Vars1.R2

/-- valuation picking the single variable as m2 -/
def ρ2 : V → M3 := fun _ => M3.m2

theorem eval_nfS_rho2 : eval ρ2 nfS.1 = M3.m1 := by
  -- nfS.1 = s = x⋆x
  simp [nfS, Step1.s, Step1.x, eval, ρ2, Models.R2M3.mul]

theorem eval_nfD_rho2 : eval ρ2 nfD.1 = M3.m0 := by
  -- nfD.1 = D = s ⋆ (x ⋆ s)
  simp [nfD, D, Step1.s, Step1.x, eval, ρ2, Models.R2M3.mul]

/-- Key result (i): R2-equivalence cannot connect nfS and nfD. -/
theorem not_NFEqR_R2_nfS_nfD :
  ¬ NFEqR (α := V) R2 nfS nfD := by
  intro h
  have hev : eval ρ2 nfS.1 = eval ρ2 nfD.1 :=
    eval_eq_of_NFEqR_R2 (ρ := ρ2) (x := nfS) (y := nfD) h
  have hs : eval ρ2 nfS.1 = M3.m1 := eval_nfS_rho2
  have hd : eval ρ2 nfD.1 = M3.m0 := eval_nfD_rho2
  have h_eq : M3.m1 = M3.m0 := by
    -- rewrite hev by the computed values
    simp [hs, hd] at hev
  have h_neq : M3.m1 ≠ M3.m0 := by decide
  exact h_neq h_eq

/-- Therefore, R2 is incomplete for NFRel (explicit witness). -/
theorem R2_incomplete_for_NFRel :
  ∃ x y : NormalForm V,
    x.1 ≠ y.1 ∧ NFRel (α := V) x y ∧ ¬ NFEqR (α := V) R2 x y := by
  refine ⟨nfS, nfD, nfS_ne_nfD, nfRel_nfS_nfD, ?_⟩
  exact not_NFEqR_R2_nfS_nfD

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
