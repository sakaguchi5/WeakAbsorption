import WeakAbsorption.Core.Algebra
import WeakAbsorption.Core.Equational
/-!
LAYER: CORE (WAA as Quotient of RedEq)
MUST NOT import: Termination / Canonical / Semantics / Free
/ Universal / Completeness / NormalFormGenerators / Examples
MAY import: Algebra / Equational (and minimal Mathlib.Tactic)
Goal: upstream-safe module that Semantics/Free can import without dragging choice/termination.
-/
open WeakAbsorption.Closure

namespace WeakAbsorption
/-! ############################################################
## Quotient algebra: WAA
############################################################ -/
abbrev WAA (α : Type) := Quot (@RedEq α)
namespace WAA
def mulTerm (t₁ : Term α) (b : WAA α) : WAA α :=
  Quot.lift
    (fun t₂ => Quot.mk RedEq (Term.op t₁ t₂))
    (fun _ _ h₂ =>
      Quot.sound (RedEq_op_right t₁ h₂))
    b
theorem mulTerm_congr_left
  (b : WAA α)
  (t₁ t₁' : Term α)
  (h : RedEq t₁ t₁') :
  mulTerm t₁ b = mulTerm t₁' b := by
  induction b using Quot.ind
  case mk t₂ =>
    exact Quot.sound (RedEq_op_left t₂ h)
def mul (a b : WAA α) : WAA α :=
  Quot.lift
    (fun t₁ => mulTerm t₁ b)
    (fun _ _ h => mulTerm_congr_left b _ _ h)
    a

instance : Mul (WAA α) := ⟨mul⟩

@[simp] theorem mk_mul_mk (t₁ t₂ : Term α) :
    ((Quot.mk RedEq t₁ : WAA α) * (Quot.mk RedEq t₂ : WAA α))
      = Quot.mk RedEq (Term.op t₁ t₂) := by
  rfl
@[simp] theorem mk_C1 (x y : Term α) :
  (Quot.mk RedEq ((x.op y).op y) : WAA α)
  =
  Quot.mk RedEq (x.op y) := by
  apply RedEq.sound_step
  exact RedStep.C1 _ _

@[simp] theorem mk_C2 (x y z : Term α) :
  (Quot.mk RedEq (((x.op y).op z).op (y.op z)) : WAA α)
  =
  Quot.mk RedEq ((x.op y).op z) := by
  apply RedEq.sound_step
  exact RedStep.C2p _ _ _

@[simp] theorem mul_C2
  (x y z : Term α) :
  (((Quot.mk RedEq x : WAA α) * Quot.mk RedEq y) * Quot.mk RedEq z)
    * (Quot.mk RedEq y * Quot.mk RedEq z)
  =
  ((Quot.mk RedEq x : WAA α) * Quot.mk RedEq y) * Quot.mk RedEq z := by
  simp


theorem weak_absorption₁ (a b : WAA α) :
  (a * b) * b = a * b := by
  induction a using Quot.ind
  induction b using Quot.ind
  apply RedEq.sound_step
  exact RedStep.C1 _ _
theorem weak_absorption₂ (a b c : WAA α) :
  ((a * b) * c) * (b * c) = (a * b) * c := by
  induction a using Quot.ind
  induction b using Quot.ind
  induction c using Quot.ind
  apply RedEq.sound_step
  exact RedStep.C2p _ _ _

/-- Generators: η : α → WAA α. -/
def eta {α : Type} (a : α) : WAA α :=
  Quot.mk RedEq (Term.var a)

@[simp] theorem eta_def {α : Type} (a : α) :
  WAA.eta a = Quot.mk RedEq (Term.var a) := rfl


def proj : Term α → WAA α :=
  Quot.mk RedEq

theorem proj_sound (t u : Term α) :
  RedEq t u → proj t = proj u :=
by
  intro h
  exact Quot.sound h

-- これを定義しておくと便利です
theorem RedEq.symm  {t u : Term α} (h : RedEq t u) : RedEq u t := Closure.EqvGen.symm _ _ h
theorem RedEq.trans  {t u v : Term α} (h1 : RedEq t u) (h2 : RedEq u v)
: RedEq t v := Closure.EqvGen.trans _ _ _ h1 h2

theorem RedEq.refl {t : Term α} : RedEq t t :=
  EqvGen.refl t

-- 補題の引数順序を「Quot.lift を2回ネストする」形に合わせておくと楽になります
-- （left/right の well-definedness を別々に渡し、外側では funext が出ます）
theorem projRel_well_defined_left {t₁ t₂ : Term α} (h : RedEq t₁ t₂) (u : Term α) :
    RedEq t₁ u = RedEq t₂ u :=
  propext ⟨(RedEq.trans (RedEq.symm h) ·), (RedEq.trans h ·)⟩

theorem projRel_well_defined_right {u₁ u₂ : Term α} (h : RedEq u₁ u₂) (t : Term α) :
    RedEq t u₁ = RedEq t u₂ :=
  propext ⟨(RedEq.trans · h), (RedEq.trans · (RedEq.symm h))⟩

-- u : WAA α (= Quot RedEq) 版の left well-defined
theorem projRel_well_defined_left_WAA
  {t₁ t₂ : Term α} (ht : RedEq t₁ t₂) (u : WAA α) :
    (Quot.lift
        (fun u : Term α => RedEq t₁ u)
        (fun _u₁ _u₂ hu => projRel_well_defined_right (α := α) hu t₁)
        u)
    =
    (Quot.lift
        (fun u : Term α => RedEq t₂ u)
        (fun _u₁ _u₂ hu => projRel_well_defined_right (α := α) hu t₂)
        u)
  :=
by
  -- u を代表元に落として Term 版の補題を適用
  refine Quot.inductionOn u (fun u : Term α => ?_)
  exact projRel_well_defined_left (α := α) ht u


-- 補題が通っている前提で、Quot.lift を2回ネストして WAA α → WAA α → Prop を定義します
-- （Lean 4 core には Quot.lift₂ は無いので、この形が core-only の基本形です）
private def projRel : WAA α → WAA α → Prop :=
  Quot.lift
    (fun t : Term α =>
      Quot.lift
        (fun u : Term α => RedEq t u)
        (fun _u₁ _u₂ hu =>
          projRel_well_defined_right (α := α) hu t
        )
    )
        (fun _t₁ _t₂ ht =>
      funext (fun u =>
        projRel_well_defined_left_WAA (α := α) ht u
      )
    )

@[simp]
theorem projRel_proj (t u : Term α) :
  projRel (proj t) (proj u) = RedEq t u :=
rfl

theorem proj_complete (t u : Term α) :
    proj t = proj u → RedEq t u :=
by
  intro h
  -- 1. ゴールを projRel (proj t) (proj u) に移す（projRel_proj）
  -- 2. h : proj t = proj u で transport して reflexive case に落とす
  -- 3. 最後は reflexive goal（RedEq.refl 相当）を simp で閉じる
  rw [← projRel_proj t u]
  rw [h]
  simp [projRel_proj]

theorem proj_eq_iff (t u : Term α) :
  proj t = proj u ↔ RedEq t u := by
  constructor
  · exact proj_complete (α := α) t u
  · exact proj_sound (α := α) t u

@[simp] theorem proj_op (t u : Term α) :
  proj (Term.op t u)
  =
  mul (proj t) (proj u) := by
  rfl

@[simp] theorem proj_op_mul (t u : Term α) :
  proj (Term.op t u)
  =
  proj t * proj u := by
  rfl

@[simp] theorem proj_var (a : α) :
  proj (Term.var a) = WAA.eta a := rfl

def c12Alg (α : Type) : C12Algebra (WAA α) :=
{ op := (fun x y : WAA α => x * y)
  C1 := by
    intro a b
    simpa using (weak_absorption₁ (α := α) a b)
  C2p := by
    intro a b c
    simpa using (weak_absorption₂ (α := α) a b c)
}

end WAA
end WeakAbsorption
