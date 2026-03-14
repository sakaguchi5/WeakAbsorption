import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace StripLite

open WeakAbsorption

section
variable {α : Type} [DecidableEq α]

/-!
A lightweight “common outer context stripping” utility for Proof-side usage.

Design goals:
- Purely structural on `Term`.
- No maximality / uniqueness claims.
- Guarantees only correctness of the returned triple `(C, u0, v0)`:
    u = plug C u0  and  v = plug C v0.
- This is enough to reason “context variants are orbit images of a core pair”.
-/

/-- `stripOnce u v` removes one common outer layer if possible. -/
def stripOnce : Term α → Term α → (Ctx α × Term α × Term α)
  | .var a, .var b =>
      (Ctx.hole, Term.var a, Term.var b)

  | .op u1 u2, .op v1 v2 =>
      -- If the *right* children match, strip a left-context.
      if _hR : u2 = v2 then
        (Ctx.left Ctx.hole u2, u1, v1)
      else
      -- If the *left* children match, strip a right-context.
      if _hL : u1 = v1 then
        (Ctx.right u1 Ctx.hole, u2, v2)
      else
        (Ctx.hole, Term.op u1 u2, Term.op v1 v2)

  | u, v =>
      (Ctx.hole, u, v)

/--
Compose contexts: `comp D C` means “first plug into C, then into D”.

(We keep this local to avoid importing Orbit.lean, and because we only need it for stripping.)
-/
def Ctx.comp : Ctx α → Ctx α → Ctx α
  | .hole,        C => C
  | .left D r,    C => .left (Ctx.comp D C) r
  | .right l D,   C => .right l (Ctx.comp D C)

omit [DecidableEq α] in
/-- Plug law for `Ctx.comp`. -/
theorem Ctx.plug_comp (D C : Ctx α) (t : Term α) :
  Ctx.plug D (Ctx.plug C t) = Ctx.plug (Ctx.comp D C) t := by
  induction D with
  | hole =>
      simp [Ctx.comp, Ctx.plug]
  | left D r ih =>
      simp [Ctx.comp, Ctx.plug, ih]
  | right l D ih =>
      simp [Ctx.comp, Ctx.plug, ih]

/--
Iteratively strip outer contexts while progress is made (fuel-bounded).
No maximality/uniqueness claims; only soundness is proven.
-/
def stripMany (fuel : Nat) (u v : Term α) : Ctx α × Term α × Term α :=
  match fuel with
  | 0 => (Ctx.hole, u, v)
  | fuel + 1 =>
      let (C1, u1, v1) := stripOnce (α := α) u v
      match C1 with
      | .hole => (Ctx.hole, u, v)
      | _ =>
          let (C2, u2, v2) := stripMany fuel u1 v1
          (Ctx.comp (α := α) C1 C2, u2, v2)
/--
Soundness of `stripOnce`:

Let `(C,u0,v0) := stripOnce u v`.
Then `u = plug C u0` and `v = plug C v0`.
-/
theorem stripOnce_sound (u v : Term α) :
  let r := stripOnce (α := α) u v
  u = Ctx.plug r.1 r.2.1 ∧ v = Ctx.plug r.1 r.2.2 := by
  -- split cases on u,v
  cases u <;> cases v <;> simp [stripOnce, Ctx.plug]
  · -- op/op case: need to split the nested ifs
    -- simp will leave by_cases goals; do them explicitly
    rename_i u1 u2 v1 v2
    by_cases hR : u2 = v2
    · simp [hR, Ctx.plug]
    · by_cases hL : u1 = v1
      · simp [hR, hL, Ctx.plug]
      · simp [hR, hL, Ctx.plug]
--left 分岐を補題化
private theorem stripMany_sound_left_case
  (fuel : Nat)
  {u v : Term α}
  {C : Ctx α} {r u1 v1 : Term α}
  {C2 : Ctx α} {u2 v2 : Term α}
  (h1 : stripOnce (α := α) u v = (Ctx.left C r, u1, v1))
  (h2 : stripMany (α := α) fuel u1 v1 = (C2, u2, v2))
  (hs2 : u1 = Ctx.plug C2 u2 ∧ v1 = Ctx.plug C2 v2) :
  u = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1 (stripMany (α := α) (Nat.succ fuel) u v).2.1
  ∧ v = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1 (stripMany (α := α) (Nat.succ fuel) u v).2.2 :=
by
  -- first-step soundness
  have hs1 : u = Ctx.plug (Ctx.left C r) u1 ∧ v = Ctx.plug (Ctx.left C r) v1 := by
    have hs := stripOnce_sound (α := α) u v
    simpa [h1] using hs
  -- unfold stripMany at succ fuel
  have hstrip :
      stripMany (α := α) (Nat.succ fuel) u v
        = (Ctx.comp (α := α) (Ctx.left C r) C2, u2, v2) := by
    simp [stripMany, h1, h2]

  refine ⟨?_, ?_⟩
  · calc
      u = Ctx.plug (Ctx.left C r) u1 := hs1.1
      _ = Ctx.plug (Ctx.left C r) (Ctx.plug C2 u2) := by simp [hs2.1]
      _ = Ctx.plug (Ctx.comp (α := α) (Ctx.left C r) C2) u2 := by
            simp [Ctx.plug_comp]
      _ = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1
            (stripMany (α := α) (Nat.succ fuel) u v).2.1 := by
            simp [hstrip]
  · calc
      v = Ctx.plug (Ctx.left C r) v1 := hs1.2
      _ = Ctx.plug (Ctx.left C r) (Ctx.plug C2 v2) := by simp [hs2.2]
      _ = Ctx.plug (Ctx.comp (α := α) (Ctx.left C r) C2) v2 := by
            simp [Ctx.plug_comp]
      _ = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1
            (stripMany (α := α) (Nat.succ fuel) u v).2.2 := by
            simp [hstrip]

--right 分岐を補題化
private theorem stripMany_sound_right_case
  (fuel : Nat)
  {u v : Term α}
  {l : Term α} {C : Ctx α} {u1 v1 : Term α}
  {C2 : Ctx α} {u2 v2 : Term α}
  (h1 : stripOnce (α := α) u v = (Ctx.right l C, u1, v1))
  (h2 : stripMany (α := α) fuel u1 v1 = (C2, u2, v2))
  (hs2 : u1 = Ctx.plug C2 u2 ∧ v1 = Ctx.plug C2 v2) :
  u = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1 (stripMany (α := α) (Nat.succ fuel) u v).2.1
  ∧ v = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1 (stripMany (α := α) (Nat.succ fuel) u v).2.2 :=
by
  -- first-step soundness
  have hs1 : u = Ctx.plug (Ctx.right l C) u1 ∧ v = Ctx.plug (Ctx.right l C) v1 := by
    have hs := stripOnce_sound (α := α) u v
    simpa [h1] using hs
  -- unfold stripMany at succ fuel
  have hstrip :
      stripMany (α := α) (Nat.succ fuel) u v
        = (Ctx.comp (α := α) (Ctx.right l C) C2, u2, v2) := by
    simp [stripMany, h1, h2]
  refine ⟨?_, ?_⟩
  · calc
      u = Ctx.plug (Ctx.right l C) u1 := hs1.1
      _ = Ctx.plug (Ctx.right l C) (Ctx.plug C2 u2) := by simp [hs2.1]
      _ = Ctx.plug (Ctx.comp (α := α) (Ctx.right l C) C2) u2 := by
            simp [Ctx.plug_comp]
      _ = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1
            (stripMany (α := α) (Nat.succ fuel) u v).2.1 := by
            simp [hstrip]
  · calc
      v = Ctx.plug (Ctx.right l C) v1 := hs1.2
      _ = Ctx.plug (Ctx.right l C) (Ctx.plug C2 v2) := by simp [hs2.2]
      _ = Ctx.plug (Ctx.comp (α := α) (Ctx.right l C) C2) v2 := by
            simp [Ctx.plug_comp]
      _ = Ctx.plug (stripMany (α := α) (Nat.succ fuel) u v).1
            (stripMany (α := α) (Nat.succ fuel) u v).2.2 := by
            simp [hstrip]
/--
Soundness of `stripMany`:

Let `(C,u0,v0) := stripMany fuel u v`.
Then `u = plug C u0` and `v = plug C v0`.
-/
theorem stripMany_sound (fuel : Nat) (u v : Term α) :
  u = Ctx.plug (stripMany (α := α) fuel u v).1 (stripMany (α := α) fuel u v).2.1
  ∧ v = Ctx.plug (stripMany (α := α) fuel u v).1 (stripMany (α := α) fuel u v).2.2 := by
  induction fuel generalizing u v with
  | zero =>
      simp [stripMany, Ctx.plug]
  | succ fuel ih =>
      cases h1 : stripOnce (α := α) u v with
      | mk C1 p =>
        cases p with
        | mk u1 v1 =>
          cases C1 with
          | hole =>
              simp [stripMany, h1, Ctx.plug]
          | left C r =>
              cases h2 : stripMany (α := α) fuel u1 v1 with
              | mk C2 p2 =>
                cases p2 with
                | mk u2 v2 =>
                  have hs2 : u1 = Ctx.plug C2 u2 ∧ v1 = Ctx.plug C2 v2 := by
                    have hs := ih (u := u1) (v := v1)
                    simpa [h2] using hs
                  have h1' : stripOnce (α := α) u v = (Ctx.left C r, u1, v1) := by
                    simpa using h1
                  have h2' : stripMany (α := α) fuel u1 v1 = (C2, u2, v2) := by
                    simpa using h2
                  exact stripMany_sound_left_case (α := α) fuel (u := u) (v := v)
                    (C := C) (r := r) (u1 := u1) (v1 := v1) (C2 := C2) (u2 := u2) (v2 := v2)
                    h1' h2' hs2
          | right l C =>
              cases h2 : stripMany (α := α) fuel u1 v1 with
              | mk C2 p2 =>
                cases p2 with
                | mk u2 v2 =>
                  have hs2 : u1 = Ctx.plug C2 u2 ∧ v1 = Ctx.plug C2 v2 := by
                    have hs := ih (u := u1) (v := v1)
                    simpa [h2] using hs
                  have h1' : stripOnce (α := α) u v = (Ctx.right l C, u1, v1) := by
                    simpa using h1
                  have h2' : stripMany (α := α) fuel u1 v1 = (C2, u2, v2) := by
                    simpa using h2
                  exact stripMany_sound_right_case (α := α) fuel (u := u) (v := v)
                    (l := l) (C := C) (u1 := u1) (v1 := v1) (C2 := C2) (u2 := u2) (v2 := v2)
                    h1' h2' hs2


end

end StripLite
end Generators
end Proof
end WeakAbsorption
