import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Patterns

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
`P5(x,p,z) := L ⋆ L` where `L := ((x ⋆ (p ⋆ z)) ⋆ z)`.

This file only establishes a negative fact:
`P5` is not a root-instance of any of the four existing R4 pattern families
`sqAbsorbPat`, `sqStablePat`, `decorPat`, `c2c1Pat`.
-/
def P5Term {α : Type} (x p z : Term α) : Term α :=
  let L := (x.op (p.op z)).op z
  L.op L

/--
No finite term can satisfy `u = x ⋆ (p ⋆ u)`.
This is the right-self-embedding obstruction.
-/
private theorem no_eq_op_right_nest {α : Type} :
    ∀ (u x p : Term α), u ≠ x.op (p.op u)
  | .var _, _, _ => by
      intro h
      cases h
  | .op u₁ u₂, x, p => by
      intro h
      injection h with _ hR
      exact no_eq_op_right_nest u₂ p u₁ hR

mutual
/--
No finite term can satisfy `u = x ⋆ (u ⋆ z)`.
This is the middle-self-embedding obstruction.
-/
private theorem no_eq_op_mid_self {α : Type} :
    ∀ (u x z : Term α), u ≠ x.op (u.op z)
  | .var _, _, _ => by
      intro h
      cases h
  | .op u₁ u₂, x, z => by
      intro h
      injection h with _ hR
      exact no_eq_op_left_self u₂ u₁ z hR

/--
No finite term can satisfy `u = (a ⋆ u) ⋆ b`.
This auxiliary obstruction is used to prove `no_eq_op_mid_self`.
-/
private theorem no_eq_op_left_self {α : Type} :
    ∀ (u a b : Term α), u ≠ (a.op u).op b
  | .var _, _, _ => by
      intro h
      cases h
  | .op u₁ u₂, a, b => by
      intro h
      injection h with hL _
      exact no_eq_op_mid_self u₁ a u₂ hL
end

/-- `P5` is not an instance of `sqAbsorbPat`. -/
theorem no_sqAbsorb_root_P5 {α : Type} (x p z : Term α) :
    NoRootInstance sqAbsorbPat (P5Term x p z) := by
  intro σ hEq
  dsimp [P5Term, sqAbsorbPat, Pat.inst] at hEq
  injection hEq with _ hR
  injection hR with hRM hRZ
  have hz : z = x.op (p.op z) := by
    calc
      z = σ 1 := hRZ.symm
      _ = x.op (p.op z) := hRM
  exact no_eq_op_right_nest z x p hz

/-- `P5` is not an instance of `sqStablePat`. -/
theorem no_sqStable_root_P5 {α : Type} (x p z : Term α) :
    NoRootInstance sqStablePat (P5Term x p z) := by
  intro σ hEq
  dsimp [P5Term, sqStablePat, Pat.inst] at hEq
  let L : Term α := (x.op (p.op z)).op z
  injection hEq with hL hR
  rw [hR] at hL
  have hL' : ((σ 0).op L).op (L.op L) = L := by
    simpa [L] using hL
  exact (no_eq_op_left_self L (σ 0) (L.op L)) hL'.symm

/-- `P5` is not an instance of `decorPat`. -/
theorem no_decor_root_P5 {α : Type} (x p z : Term α) :
    NoRootInstance decorPat (P5Term x p z) := by
  intro σ hEq
  dsimp [P5Term, decorPat, Pat.inst] at hEq
  let L : Term α := (x.op (p.op z)).op z
  injection hEq with hL hR
  -- hL : (σ 0).op (σ 1) = L
  -- hR : (σ 1).op ((σ 1).op (σ 1)) = L
  have hL' : (σ 0).op (σ 1) = L := by simpa [L] using hL
  have hR' : (σ 1).op ((σ 1).op (σ 1)) = L := by simpa [L] using hR
  injection hL' with hL1 hL2
  -- hL1 : σ 0 = x.op (p.op z)
  -- hL2 : σ 1 = z
  rw [hL2] at hR'
  have hz : z = x.op (p.op z) := by
    injection hR' with hz _
  exact no_eq_op_right_nest z x p hz

/-- `P5` is not an instance of `c2c1Pat`. -/
theorem no_c2c1_root_P5 {α : Type} (x p z : Term α) :
    NoRootInstance c2c1Pat (P5Term x p z) := by
  intro σ hEq
  dsimp [P5Term, c2c1Pat, Pat.inst] at hEq
  let L : Term α := (x.op (p.op z)).op z
  injection hEq with hL hR
  -- hL : ((σ 0).op ((σ 1).op (σ 2))).op (σ 2) = L
  -- hR : (σ 1).op (σ 2) = L
  have hL' : ((σ 0).op ((σ 1).op (σ 2))).op (σ 2) = L := by
    simpa [L] using hL
  have hR' : (σ 1).op (σ 2) = L := by
    simpa [L] using hR
  injection hR' with hR1 hR2
  -- hR1 : σ 1 = x.op (p.op z)
  -- hR2 : σ 2 = z
  rw [hR1, hR2] at hL'
  have hcore : ((x.op (p.op z)).op z) = p.op z := by
    injection hL' with hLL _
    injection hLL with _ hcore
  have hp : p = x.op (p.op z) := by
    injection hcore with hp _
    exact hp.symm
  exact no_eq_op_mid_self p x z hp

/-- Concrete root exclusion for `sqAbsorbPat`. -/
theorem no_sqAbsorb_root_eq_P5 {α : Type} (x p z : Term α) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z :=
  no_sqAbsorb_root_eq_of_no_instance (target := P5Term x p z) (no_sqAbsorb_root_P5 x p z)

/-- Concrete root exclusion for `sqStablePat`. -/
theorem no_sqStable_root_eq_P5 {α : Type} (x p z : Term α) :
    ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z :=
  no_sqStable_root_eq_of_no_instance (target := P5Term x p z) (no_sqStable_root_P5 x p z)

/-- Concrete root exclusion for `decorPat`. -/
theorem no_decor_root_eq_P5 {α : Type} (x p z : Term α) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z :=
  no_decor_root_eq_of_no_instance (target := P5Term x p z) (no_decor_root_P5 x p z)

/-- Concrete root exclusion for `c2c1Pat`. -/
theorem no_c2c1_root_eq_P5 {α : Type} (x p z : Term α) :
    ∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z :=
  no_c2c1_root_eq_of_no_instance (target := P5Term x p z) (no_c2c1_root_P5 x p z)

theorem P5_root_excluded_from_R4_patterns {α : Type} (x p z : Term α) :
    NoRootInstance sqAbsorbPat (P5Term x p z) ∧
    NoRootInstance sqStablePat (P5Term x p z) ∧
    NoRootInstance decorPat (P5Term x p z) ∧
    NoRootInstance c2c1Pat (P5Term x p z) := by
  refine ⟨no_sqAbsorb_root_P5 x p z, no_sqStable_root_P5 x p z,
    no_decor_root_P5 x p z, no_c2c1_root_P5 x p z⟩

theorem P5_is_self_square {α : Type} (x p z : Term α) :
    ∃ L : Term α, P5Term x p z = L.op L := by
  refine ⟨(x.op (p.op z)).op z, ?_⟩
  simp [P5Term]

theorem P5_root_excluded_from_R4_patterns_concrete {α : Type} (x p z : Term α) :
    (∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
    (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
    (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
    (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z) := by
  refine ⟨
    no_sqAbsorb_root_eq_P5 x p z,
    no_sqStable_root_eq_P5 x p z,
    no_decor_root_eq_P5 x p z,
    no_c2c1_root_eq_P5 x p z
  ⟩

/--
`P5` is not merely "some square"; it is the square of the whole fragment
`((x ⋆ (p ⋆ z)) ⋆ z)`.
-/
theorem P5_has_canonical_square_core {α : Type} (x p z : Term α) :
    P5Term x p z = (((x.op (p.op z)).op z).op ((x.op (p.op z)).op z)) := by
  simp [P5Term]

theorem P5_right_reappearance_is_whole_fragment {α : Type} (x p z : Term α) :
    ∃ L : Term α,
      L = (x.op (p.op z)).op z ∧
      P5Term x p z = L.op L := by
  refine ⟨(x.op (p.op z)).op z, rfl, ?_⟩
  simp [P5Term]


end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
