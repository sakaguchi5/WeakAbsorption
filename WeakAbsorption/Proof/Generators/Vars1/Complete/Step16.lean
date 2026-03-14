import WeakAbsorption.Proof.Generators.Vars1.Complete.Step15
import WeakAbsorption.Proof.Generators.NormalFormGenerators

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step16

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.WAA

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step15

/-!
Step16: “Two-kernel closure fails” (vars=1).

Counterexample based on the Decor phenomenon:
  D := (x⋆x)⋆(x⋆(x⋆x)).

We have NFRel D s, but (s,D) cannot be obtained by plugging a context
into any of the four Step15 core templates (pure size obstructions).
-/

section

/-- Decor witness: (x⋆x)⋆(x⋆(x⋆x)) -/
def D : Term V := s ⋆ (x ⋆ s)

theorem size_D : size D = 9 := by
  simp [D, s, x, size]

private theorem x_normal : Normal (α := V) x := by
  intro u hu
  cases hu with
  | step _ _ hs =>
      cases hs

private theorem not_C1_x_x : ¬ IsC1Root (α := V) x x := by
  rintro ⟨w, hw⟩
  cases hw

private theorem not_C2_x_x : ¬ IsC2pRoot (α := V) x x := by
  simp [IsC2pRoot, x]

private theorem s_normal : Normal (α := V) s := by
  exact (Normal_op_iff (α := V) x x).2
    ⟨x_normal, x_normal, not_C1_x_x, not_C2_x_x⟩

private theorem not_C1_x_s : ¬ IsC1Root (α := V) x s := by
  rintro ⟨w, hw⟩
  cases hw

private theorem not_C2_x_s : ¬ IsC2pRoot (α := V) x s := by
  dsimp [IsC2pRoot, s, x]
  rintro ⟨w, hw⟩
  cases hw

private theorem xs_normal : Normal (α := V) (x ⋆ s) := by
  exact (Normal_op_iff (α := V) x s).2
    ⟨x_normal, s_normal, not_C1_x_s, not_C2_x_s⟩

private theorem not_C1_s_xs : ¬ IsC1Root (α := V) s (x ⋆ s) := by
  rintro ⟨w, hw⟩
  dsimp [s, x] at hw
  injection hw with hL hR
  cases hR

private theorem not_C2_s_xs : ¬ IsC2pRoot (α := V) s (x ⋆ s) := by
  dsimp [IsC2pRoot, s, x, D]
  rintro ⟨w, hw⟩
  injection hw with h1 h2
  cases h1

private theorem D_normal : Normal (α := V) D := by
  exact (Normal_op_iff (α := V) s (x ⋆ s)).2
    ⟨s_normal, xs_normal, not_C1_s_xs, not_C2_s_xs⟩

def nfS : NormalForm V := ⟨s, s_normal⟩
def nfD : NormalForm V := ⟨D, D_normal⟩

theorem nfS_ne_nfD : nfS.1 ≠ nfD.1 := by
  intro h
  have hs : size nfS.1 = size nfD.1 := congrArg size h
  simp [nfS, nfD, size_s, size_D] at hs

theorem nfRel_nfS_nfD : NFRel (α := V) nfS nfD := by
  dsimp [NFRel, nfS, nfD, D]
  have h : RedEq (α := V) (s ⋆ (x ⋆ s)) s := by
    simpa [s] using (RedEq_decor_uuu (α := V) (t := x) (u := x))
  exact EqvGen.symm _ _ h
private theorem size_le_of_ctxStepNF_left
  {a b : Term V} {x y : NormalForm V} :
  CtxStepNF a b x y → size a ≤ size x.1 := by
  rintro ⟨C, hx, hy⟩
  have h0 : size x.1 = size (Ctx.plug C a) := congrArg size hx
  have h1 : size (Ctx.plug C a) = size a + Ctx.sizeOffset (α := V) C := by
    simpa using (size_plug_bound (C := C) (t := a))
  -- size x = size a + off だから size a ≤ size x
  have : size a ≤ size a + Ctx.sizeOffset (α := V) C := Nat.le_add_right _ _
  -- h0,h1 で右辺を size x に置換
  simp [h0, h1,this]

private theorem size_le_of_ctxStepNF_right
  {a b : Term V} {x y : NormalForm V} :
  CtxStepNF a b x y → size b ≤ size y.1 := by
  rintro ⟨C, hx, hy⟩
  have h0 : size y.1 = size (Ctx.plug C b) := congrArg size hy
  have h1 : size (Ctx.plug C b) = size b + Ctx.sizeOffset (α := V) C := by
    simpa using (size_plug_bound (C := C) (t := b))
  have : size b ≤ size b + Ctx.sizeOffset (α := V) C := Nat.le_add_right _ _
  simp [h0, h1,this]

private theorem size_lt_op_right (t u : Term V) : size u < size (t ⋆ u) := by
  -- size (t⋆u) = size t + size u + 1
  -- よって size u < ...
  simp [size]
  omega

private theorem size_lt_op_left (t u : Term V) : size t < size (t ⋆ u) := by
  simp [size]
  omega
private theorem size_s_lt_size_A : size s < size A := by
  -- A = s⋆s
  simpa [A] using (size_lt_op_left (t := s) (u := s))

private theorem size_A_lt_size_Au : size A < size Au := by
  -- Au = A⋆x
  simpa [Au] using (size_lt_op_left (t := A) (u := x))

private theorem size_A_lt_size_D : size A < size D := by
  -- A = s⋆s, D = s⋆(x⋆s)
  have hs : size s < size (x ⋆ s) := by
    -- size s < size (x⋆s)（右引数が s）
    simpa using (size_lt_op_right (t := x) (u := s))
  -- size A = size s + size s + 1
  -- size D = size s + size (x⋆s) + 1
  -- hs から size A < size D
  -- ここは Nat.add_lt_add_left + Nat.succ_lt_succ を使うと綺麗
  have : size s + size s < size s + size (x ⋆ s) := Nat.add_lt_add_left hs (size s)
  -- +1 を両辺に足す
  have : size s + size s + 1 < size s + size (x ⋆ s) + 1 := Nat.succ_lt_succ this
  -- 形を整える
  simpa [A, D, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
private theorem no_ctxStep_A_s : ¬ CtxStepNF A s nfS nfD := by
  intro h
  have hle : size A ≤ size nfS.1 := size_le_of_ctxStepNF_left (a := A) (b := s) h
  -- nfS.1 = s
  have hle' : size A ≤ size s := by simpa [nfS] using hle
  have hlt : size s < size A := size_s_lt_size_A
  exact (Nat.not_le_of_gt hlt) hle'

private theorem no_ctxStep_s_A : ¬ CtxStepNF s A nfS nfD := by
  rintro ⟨C, hx, hy⟩
  -- (1) plug C s = s から offset=0
  have hsEq : s = Ctx.plug C s := by
    simpa [nfS] using hx
  have hs_size : size s = size s + Ctx.sizeOffset (α := V) C := by
    have h0 : size s = size (Ctx.plug C s) := congrArg size hsEq
    have h1 : size (Ctx.plug C s) = size s + Ctx.sizeOffset (α := V) C := by
      simpa using (size_plug_bound (C := C) (t := s))
    exact h0.trans h1
  have hoff : Ctx.sizeOffset (α := V) C = 0 := by
    have h' : size s + Ctx.sizeOffset (α := V) C = size s + 0 := by
      simpa [Nat.add_zero] using hs_size.symm
    exact Nat.add_left_cancel h'
  -- (2) hy : D = plug C A から size D = size A（offset=0 を代入）
  have hDEq : D = Ctx.plug C A := by
    simpa [nfD] using hy
  have hD_size : size D = size A + Ctx.sizeOffset (α := V) C := by
    have h0 : size D = size (Ctx.plug C A) := congrArg size hDEq
    have h1 : size (Ctx.plug C A) = size A + Ctx.sizeOffset (α := V) C := by
      simpa using (size_plug_bound (C := C) (t := A))
    exact h0.trans h1
  have hEq : size D = size A := by
    simpa [hoff, Nat.add_zero] using hD_size
  -- (3) でも size A < size D なので矛盾
  exact (Nat.ne_of_lt size_A_lt_size_D) (hEq.symm)

private theorem no_ctxStep_Au_A : ¬ CtxStepNF Au A nfS nfD := by
  intro h
  have hle : size Au ≤ size nfS.1 :=
    size_le_of_ctxStepNF_left (a := Au) (b := A) h
  have hle' : size Au ≤ size s := by
    simpa [nfS] using hle
  have hlt : size s < size Au := by
    -- Au = A⋆x かつ A = s⋆s なので s < A < Au
    exact Nat.lt_trans size_s_lt_size_A size_A_lt_size_Au
  exact (Nat.not_le_of_gt hlt) hle'

private theorem no_ctxStep_A_Au : ¬ CtxStepNF A Au nfS nfD := by
  intro h
  have hle : size A ≤ size nfS.1 :=
    size_le_of_ctxStepNF_left (a := A) (b := Au) h
  have hle' : size A ≤ size s := by
    simpa [nfS] using hle
  exact (Nat.not_le_of_gt size_s_lt_size_A) hle'

theorem twoKernel_counterexample :
  ∃ x y : NormalForm V,
    x.1 ≠ y.1 ∧ NFRel (α := V) x y ∧
    ¬ ((CtxStepNF A  s  x y) ∨ (CtxStepNF s  A  x y) ∨
       (CtxStepNF Au A  x y) ∨ (CtxStepNF A  Au x y)) := by
  refine ⟨nfS, nfD, nfS_ne_nfD, nfRel_nfS_nfD, ?_⟩
  intro h
  rcases h with h | h | h | h
  · exact no_ctxStep_A_s h
  · exact no_ctxStep_s_A h
  · exact no_ctxStep_Au_A h
  · exact no_ctxStep_A_Au h

theorem not_NFRelImpliesCtxCoreTplVars1 : ¬ NFRelImpliesCtxCoreTplVars1 := by
  intro h
  rcases twoKernel_counterexample with ⟨x, y, hne, hrel, hno⟩
  have hw := h x y hne hrel
  exact hno hw

end

end Step16
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
