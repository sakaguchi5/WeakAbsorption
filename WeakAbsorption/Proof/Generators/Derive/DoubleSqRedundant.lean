import WeakAbsorption.Core.Equational
import WeakAbsorption.Proof.Generators.NormalFormGenerators

open WeakAbsorption.Closure

/-!
NOTE:
This file proves **equational redundancy** of DoubleSq:
the DoubleSq equation is derivable in `RedEq` from SqAbsorb alone.

It does **not** prove generator redundancy on normal forms.
In particular, it remains a separate question whether
`NFDoubleSqStepCtx x y -> NFEqR R4 x y`.
-/

namespace WeakAbsorption
namespace WAA
variable {α : Type}

/--
DoubleSq is derivable from SqAbsorb alone (equational reasoning):
  ((t⋆u⁴)⋆u²) ≈ (t⋆u²)
where u² := u⋆u and u⁴ := u²⋆u².
-/
theorem RedEq_absorb_doubleSq_right_of_sqAbsorb (t u : Term α) :
  RedEq ((t.op ((u.op u).op (u.op u))).op (u.op u)) (t.op (u.op u)) := by
  let uu : Term α := u.op u
  let u4 : Term α := uu.op uu

  -- (1) u⁴ ≈ u²  (SqAbsorb with t=u, u=u)
  have hu4 : RedEq u4 uu := by
    simpa [uu, u4] using (RedEq_absorb_sq_right (α := α) (t := u) (u := u))

  -- (2) t⋆u⁴ ≈ t⋆u²
  have htu : RedEq (t.op u4) (t.op uu) :=
    RedEq_op_right (α := α) (t₁ := t) hu4

  -- lift to ((t⋆u⁴)⋆u²) ≈ ((t⋆u²)⋆u²)
  have h1 : RedEq ((t.op u4).op uu) ((t.op uu).op uu) :=
    RedEq_op_left (α := α) (t₂ := uu) htu

  -- (3) u² ≈ u⁴  (symm)
  have huu4 : RedEq uu u4 := EqvGen.symm _ _ hu4

  -- ((t⋆u²)⋆u²) ≈ ((t⋆u²)⋆u⁴)
  have h2 : RedEq ((t.op uu).op uu) ((t.op uu).op u4) :=
    RedEq_op_right (α := α) (t₁ := (t.op uu)) huu4

  -- (4) (t⋆u²)⋆u⁴ ≈ t⋆u²  (SqAbsorb with u := u²)
  have h3 : RedEq ((t.op uu).op u4) (t.op uu) := by
    simpa [uu, u4] using (RedEq_absorb_sq_right (α := α) (t := t) (u := uu))

  -- chain
  exact EqvGen.trans _ _ _ h1 (EqvGen.trans _ _ _ h2 h3)

/-- Context version (so it matches the NFDoubleSqStepCtx packaging style). -/
theorem RedEq_absorb_doubleSq_right_ctx_of_sqAbsorb (C : Ctx α) (t u : Term α) :
  RedEq (Ctx.plug C ((t.op ((u.op u).op (u.op u))).op (u.op u)))
        (Ctx.plug C (t.op (u.op u))) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_absorb_doubleSq_right_of_sqAbsorb (α := α) (t := t) (u := u)

end WAA
end WeakAbsorption
