import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_KernelTheorems

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
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section RootBehaviorCells

/-!
This section re-exposes the root behavior table as theorem cells.
Each cell is preceded by its current registry label:
* `noRoot / varLeft`, `noRoot / globalNomatch`, `noRoot / leftShell1`, `noRoot / rightShell1`,
  `noRoot / projForceLeft`, `noRoot / projForceRight`, or `productive`.

Current pending-audit cells:
* none at this stage
-/

/-! ### xASqAPred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xASqAPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xASqAPredTerm :=
  no_sqAbsorb_root_eq_xASqAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqAPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xASqAPredTerm :=
  no_sqStable_root_eq_xASqAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqAPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xASqAPredTerm :=
  no_decor_root_eq_xASqAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqAPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xASqAPredTerm :=
  no_c2c1_root_eq_xASqAPred x0 p z0

/-! ### xASqRightPred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xASqRightPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xASqRightSPredTerm :=
  no_sqAbsorb_root_eq_xASqRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqRightPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xASqRightSPredTerm :=
  no_sqStable_root_eq_xASqRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqRightPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xASqRightSPredTerm :=
  no_decor_root_eq_xASqRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xASqRightPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xASqRightSPredTerm :=
  no_c2c1_root_eq_xASqRightPred x0 p z0

/-! ### xAStablePred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xAStablePred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xAStablePredTerm :=
  no_sqAbsorb_root_eq_xAStablePred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xAStablePred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xAStablePredTerm :=
  no_sqStable_root_eq_xAStablePred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xAStablePred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xAStablePredTerm :=
  no_decor_root_eq_xAStablePred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xAStablePred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xAStablePredTerm :=
  no_c2c1_root_eq_xAStablePred x0 p z0

/-! ### xADecorAPred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorAPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorAPredTerm :=
  no_sqAbsorb_root_eq_xADecorAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorAPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorAPredTerm :=
  no_sqStable_root_eq_xADecorAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorAPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorAPredTerm :=
  no_decor_root_eq_xADecorAPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorAPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorAPredTerm :=
  no_c2c1_root_eq_xADecorAPred x0 p z0

/-! ### xADecorLeftPred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorLeftPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorLeftSPredTerm :=
  no_sqAbsorb_root_eq_xADecorLeftPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorLeftPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorLeftSPredTerm :=
  no_sqStable_root_eq_xADecorLeftPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorLeftPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorLeftSPredTerm :=
  no_decor_root_eq_xADecorLeftPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorLeftPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorLeftSPredTerm :=
  no_c2c1_root_eq_xADecorLeftPred x0 p z0

/-! ### xADecorRightPred -/
-- registry row: sqAbsorb=noRoot / varLeft / sqStable=noRoot / varLeft / decor=noRoot / varLeft / c2c1=noRoot / varLeft

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorRightPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorRightSPredTerm :=
  no_sqAbsorb_root_eq_xADecorRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorRightPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorRightSPredTerm :=
  no_sqStable_root_eq_xADecorRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorRightPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorRightSPredTerm :=
  no_decor_root_eq_xADecorRightPred t u

-- registry cell: noRoot / varLeft
theorem rootCell_xADecorRightPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorRightSPredTerm :=
  no_c2c1_root_eq_xADecorRightPred x0 p z0

/-! ### uSqLiftAPred -/
-- registry row: sqAbsorb=noRoot / projForceLeft / sqStable=noRoot / globalNomatch / decor=noRoot / simp / c2c1=noRoot / leftShell1

-- registry cell: noRoot / projForceLeft
theorem rootCell_uSqLiftAPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uSqLiftAPredTerm :=
  no_sqAbsorb_root_eq_uSqLiftAPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uSqLiftAPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uSqLiftAPredTerm :=
  no_sqStable_root_eq_uSqLiftAPred t u

-- registry cell: noRoot / simp
theorem rootCell_uSqLiftAPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uSqLiftAPredTerm :=
  no_decor_root_eq_uSqLiftAPred t u

-- registry cell: noRoot / leftShell1
theorem rootCell_uSqLiftAPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uSqLiftAPredTerm :=
  no_c2c1_root_eq_uSqLiftAPred x0 p z0

/-! ### uSqLiftRightPred -/
-- registry row: sqAbsorb=noRoot / projForceLeft / sqStable=noRoot / globalNomatch / decor=noRoot / projForceRight / c2c1=noRoot / globalNomatch

-- registry cell: noRoot / projForceLeft
theorem rootCell_uSqLiftRightPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uSqLiftRightSPredTerm :=
  no_sqAbsorb_root_eq_uSqLiftRightPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uSqLiftRightPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uSqLiftRightSPredTerm :=
  no_sqStable_root_eq_uSqLiftRightPred t u

-- registry cell: noRoot / projForceRight
theorem rootCell_uSqLiftRightPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uSqLiftRightSPredTerm :=
  no_decor_root_eq_uSqLiftRightPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uSqLiftRightPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uSqLiftRightSPredTerm :=
  no_c2c1_root_eq_uSqLiftRightPred x0 p z0

/-! ### uDecorLiftLeftPred -/
-- registry row: sqAbsorb=noRoot / projForceLeft / sqStable=noRoot / globalNomatch / decor=noRoot / projForceRight / c2c1=noRoot / leftShell1

-- registry cell: noRoot / projForceLeft
theorem rootCell_uDecorLiftLeftPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorLiftLeftSPredTerm :=
  no_sqAbsorb_root_eq_uDecorLiftLeftPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorLiftLeftPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorLiftLeftSPredTerm :=
  no_sqStable_root_eq_uDecorLiftLeftPred t u

-- registry cell: noRoot / projForceRight
theorem rootCell_uDecorLiftLeftPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorLiftLeftSPredTerm :=
  no_decor_root_eq_uDecorLiftLeftPred t u

-- registry cell: noRoot / leftShell1
theorem rootCell_uDecorLiftLeftPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorLiftLeftSPredTerm :=
  no_c2c1_root_eq_uDecorLiftLeftPred x0 p z0

/-! ### uDecorLiftRightPred -/
-- registry row: sqAbsorb=noRoot / projForceLeft / sqStable=noRoot / globalNomatch / decor=noRoot / rightShell1 / c2c1=noRoot / leftShell1

-- registry cell: noRoot / projForceLeft
theorem rootCell_uDecorLiftRightPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorLiftRightSPredTerm :=
  no_sqAbsorb_root_eq_uDecorLiftRightPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorLiftRightPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorLiftRightSPredTerm :=
  no_sqStable_root_eq_uDecorLiftRightPred t u

-- registry cell: noRoot / rightShell1
theorem rootCell_uDecorLiftRightPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorLiftRightSPredTerm :=
  no_decor_root_eq_uDecorLiftRightPred t u

-- registry cell: noRoot / leftShell1
theorem rootCell_uDecorLiftRightPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorLiftRightSPredTerm :=
  no_c2c1_root_eq_uDecorLiftRightPred x0 p z0

/-! ### uDecorRightPred -/
-- registry row: sqAbsorb=noRoot / projForceRight / sqStable=noRoot / globalNomatch / decor=noRoot / projForceRight / c2c1=noRoot / globalNomatch

-- registry cell: noRoot / projForceRight
theorem rootCell_uDecorRightPred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorRightPredTerm :=
  no_sqAbsorb_root_eq_uDecorRightPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorRightPred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorRightPredTerm :=
  no_sqStable_root_eq_uDecorRightPred t u

-- registry cell: noRoot / projForceRight
theorem rootCell_uDecorRightPred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorRightPredTerm :=
  no_decor_root_eq_uDecorRightPred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorRightPred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorRightPredTerm :=
  no_c2c1_root_eq_uDecorRightPred x0 p z0

/-! ### uStablePred -/
-- registry row: sqAbsorb=noRoot / globalNomatch / sqStable=noRoot / globalNomatch / decor=noRoot / rightShell1 / c2c1=noRoot / globalNomatch

-- registry cell: noRoot / globalNomatch
theorem rootCell_uStablePred_sqAbsorb_noRoot
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = uStablePredTerm) : False :=
  no_sqAbsorb_root_eq_uStablePred hEq

-- registry cell: noRoot / globalNomatch
theorem rootCell_uStablePred_sqStable_noRoot
    {t u : Term V}
    (hEq : (((t.op u).op (u.op u)).op u) = uStablePredTerm) : False :=
  no_sqStable_root_eq_uStablePred hEq

-- registry cell: noRoot / rightShell1
theorem rootCell_uStablePred_decor_noRoot
    {t u : Term V}
    (hEq : ((t.op u).op (u.op (u.op u))) = uStablePredTerm) : False :=
  no_decor_root_eq_uStablePred hEq

-- registry cell: noRoot / globalNomatch
theorem rootCell_uStablePred_c2c1_noRoot
    {x0 p z0 : Term V}
    (hEq : (((x0.op (p.op z0)).op z0).op (p.op z0)) = uStablePredTerm) : False :=
  no_c2c1_root_eq_uStablePred hEq

/-! ### uHolePred -/
-- registry row: sqAbsorb=productive / sqStable=noRoot / globalNomatch / decor=noRoot / globalNomatch / c2c1=productive

-- registry cell: productive
theorem rootCell_uHolePred_sqAbsorb_productive
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = uHolePredTerm) :
    t.op u = uTerm :=
  sqAbsorb_root_eq_uHolePred_forces_step_eq_uTerm hEq

-- registry cell: noRoot / globalNomatch
theorem rootCell_uHolePred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uHolePredTerm :=
  no_sqStable_root_eq_uHolePred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uHolePred_decor_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uHolePredTerm :=
  no_decor_root_eq_uHolePred t u

-- registry cell: productive
theorem rootCell_uHolePred_c2c1_productive
    {x0 p z0 : Term V}
    (hEq : (((x0.op (p.op z0)).op z0).op (p.op z0)) = uHolePredTerm) :
    ((x0.op (p.op z0)).op z0) = uTerm :=
  c2c1_root_eq_uHolePred_forces_step_eq_uTerm hEq

/-! ### uDecorHolePred -/
-- registry row: sqAbsorb=noRoot / globalNomatch / sqStable=noRoot / globalNomatch / decor=productive / c2c1=noRoot / globalNomatch

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorHolePred_sqAbsorb_noRoot
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorHolePredTerm :=
  no_sqAbsorb_root_eq_uDecorHolePred t u

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorHolePred_sqStable_noRoot
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorHolePredTerm :=
  no_sqStable_root_eq_uDecorHolePred t u

-- registry cell: productive
theorem rootCell_uDecorHolePred_decor_productive
    {t u : Term V}
    (hEq : ((t.op u).op (u.op (u.op u))) = uDecorHolePredTerm) :
    t.op u = uTerm :=
  decor_root_eq_uDecorHolePred_forces_step_eq_uTerm hEq

-- registry cell: noRoot / globalNomatch
theorem rootCell_uDecorHolePred_c2c1_noRoot
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorHolePredTerm :=
  no_c2c1_root_eq_uDecorHolePred x0 p z0

end RootBehaviorCells

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
