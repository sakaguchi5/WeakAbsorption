import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Patterns
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Registry
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Targets
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4PlugRegistry

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open ProofCore
open WAA

/-- Strategy witness for root cases that first force a substitution/constraint. -/
structure RightForcingWitness {α : Type} {n : Nat}
    (p : Pat n) (target : Term α) where
  Φ      : (Fin n → Term α) → Prop
  forces : RootMatchForces p target Φ
  refute : ∀ σ, Φ σ → Pat.inst σ p ≠ target

namespace RightForcingWitness

theorem noRootInstance
    {α : Type} {n : Nat} {p : Pat n} {target : Term α}
    (w : RightForcingWitness p target) :
    NoRootInstance p target := by
  exact ProofCore.noRootInstance_of_forces_and_refutes w.forces w.refute

end RightForcingWitness


abbrev SqAbsorbNoRootGoal {α : Type} (target : Term α) :=
  ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target

abbrev SqStableNoRootGoal {α : Type} (target : Term α) :=
  ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ target

abbrev DecorNoRootGoal {α : Type} (target : Term α) :=
  ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target

abbrev C2C1NoRootGoal {α : Type} (target : Term α) :=
  ∀ x0 p z0 : Term α, (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ target

abbrev SqAbsorbProductiveGoal {α : Type} (rootTarget stepTarget : Term α) :=
  ∀ {t u : Term α}, ((t.op u).op (u.op u)) = rootTarget → t.op u = stepTarget

abbrev SqStableProductiveGoal {α : Type} (rootTarget stepTarget : Term α) :=
  ∀ {t u : Term α}, (((t.op u).op (u.op u)).op u) = rootTarget → t.op u = stepTarget

abbrev DecorProductiveGoal {α : Type} (rootTarget stepTarget : Term α) :=
  ∀ {t u : Term α}, ((t.op u).op (u.op (u.op u))) = rootTarget → t.op u = stepTarget

abbrev C2C1ProductiveGoal {α : Type} (rootTarget stepTarget : Term α) :=
  ∀ {x0 p z0 : Term α}, (((x0.op (p.op z0)).op z0).op (p.op z0)) = rootTarget → ((x0.op (p.op z0)).op z0) = stepTarget

structure MixedRootRow
    (sqAbsorbCell : Sort _)
    (sqStableCell : Sort _)
    (decorCell : Sort _)
    (c2c1Cell : Sort _) where
  sqAbsorb : sqAbsorbCell
  sqStable : sqStableCell
  decor    : decorCell
  c2c1     : c2c1Cell

abbrev NoRootRow {α : Type} (target : Term α) : Type :=
  MixedRootRow
    (SqAbsorbNoRootGoal target)
    (SqStableNoRootGoal target)
    (DecorNoRootGoal target)
    (C2C1NoRootGoal target)

/-- The theorem-level payload expected for the SqAbsorb cell of a registry row. -/
def SqAbsorbCellCertificate : RootTarget -> RootOutcome -> Sort _
  | tg, .noRoot => SqAbsorbNoRootGoal (rootTargetTerm tg)
  | .uHolePred, .productive => SqAbsorbProductiveGoal uHolePredTerm uTerm
  | _, .productive => False

/-- The theorem-level payload expected for the SqStable cell of a registry row. -/
def SqStableCellCertificate : RootTarget -> RootOutcome -> Sort _
  | tg, .noRoot => SqStableNoRootGoal (rootTargetTerm tg)
  | _, .productive => False

/-- The theorem-level payload expected for the Decor cell of a registry row. -/
def DecorCellCertificate : RootTarget -> RootOutcome -> Sort _
  | tg, .noRoot => DecorNoRootGoal (rootTargetTerm tg)
  | .uDecorHolePred, .productive => DecorProductiveGoal uDecorHolePredTerm uTerm
  | _, .productive => False

/-- The theorem-level payload expected for the C2C1 cell of a registry row. -/
def C2C1CellCertificate : RootTarget -> RootOutcome -> Sort _
  | tg, .noRoot => C2C1NoRootGoal (rootTargetTerm tg)
  | .uHolePred, .productive => C2C1ProductiveGoal uHolePredTerm uTerm
  | _, .productive => False

/--
The theorem-level row certificate expected for a given registry row view.
This is the strong bridge from metadata (`rootRowView`) to theorem payload.
-/
def TargetRowCertificateOfView (tg : RootTarget) (view : RootRowView) : Type :=
  MixedRootRow
    (SqAbsorbCellCertificate tg view.outcomes.sqAbsorb)
    (SqStableCellCertificate tg view.outcomes.sqStable)
    (DecorCellCertificate tg view.outcomes.decor)
    (C2C1CellCertificate tg view.outcomes.c2c1)

/--
The theorem-level row certificate expected for a registered target.
Unlike the earlier target-only definition, this one is computed directly from
`rootRowView`, so registry metadata and theorem payload stay definitionally linked.
-/
abbrev TargetRowCertificate (tg : RootTarget) : Type :=
  TargetRowCertificateOfView tg (rootRowView tg)

@[simp] theorem targetRowCertificate_xASqAPred :
    TargetRowCertificate RootTarget.xASqAPred = NoRootRow xASqAPredTerm := rfl
@[simp] theorem targetRowCertificate_xASqRightPred :
    TargetRowCertificate RootTarget.xASqRightPred = NoRootRow xASqRightSPredTerm := rfl
@[simp] theorem targetRowCertificate_xAStablePred :
    TargetRowCertificate RootTarget.xAStablePred = NoRootRow xAStablePredTerm := rfl
@[simp] theorem targetRowCertificate_xADecorAPred :
    TargetRowCertificate RootTarget.xADecorAPred = NoRootRow xADecorAPredTerm := rfl
@[simp] theorem targetRowCertificate_xADecorLeftPred :
    TargetRowCertificate RootTarget.xADecorLeftPred = NoRootRow xADecorLeftSPredTerm := rfl
@[simp] theorem targetRowCertificate_xADecorRightPred :
    TargetRowCertificate RootTarget.xADecorRightPred = NoRootRow xADecorRightSPredTerm := rfl
@[simp] theorem targetRowCertificate_uSqLiftAPred :
    TargetRowCertificate RootTarget.uSqLiftAPred = NoRootRow uSqLiftAPredTerm := rfl
@[simp] theorem targetRowCertificate_uSqLiftRightPred :
    TargetRowCertificate RootTarget.uSqLiftRightPred = NoRootRow uSqLiftRightSPredTerm := rfl
@[simp] theorem targetRowCertificate_uDecorLiftLeftPred :
    TargetRowCertificate RootTarget.uDecorLiftLeftPred = NoRootRow uDecorLiftLeftSPredTerm := rfl
@[simp] theorem targetRowCertificate_uDecorLiftRightPred :
    TargetRowCertificate RootTarget.uDecorLiftRightPred = NoRootRow uDecorLiftRightSPredTerm := rfl
@[simp] theorem targetRowCertificate_uDecorRightPred :
    TargetRowCertificate RootTarget.uDecorRightPred = NoRootRow uDecorRightPredTerm := rfl
@[simp] theorem targetRowCertificate_uStablePred :
    TargetRowCertificate RootTarget.uStablePred = NoRootRow uStablePredTerm := rfl
@[simp] theorem targetRowCertificate_uHolePred :
    TargetRowCertificate RootTarget.uHolePred =
      MixedRootRow
        (SqAbsorbProductiveGoal uHolePredTerm uTerm)
        (SqStableNoRootGoal uHolePredTerm)
        (DecorNoRootGoal uHolePredTerm)
        (C2C1ProductiveGoal uHolePredTerm uTerm) := rfl
@[simp] theorem targetRowCertificate_uDecorHolePred :
    TargetRowCertificate RootTarget.uDecorHolePred =
      MixedRootRow
        (SqAbsorbNoRootGoal uDecorHolePredTerm)
        (SqStableNoRootGoal uDecorHolePredTerm)
        (DecorProductiveGoal uDecorHolePredTerm uTerm)
        (C2C1NoRootGoal uDecorHolePredTerm) := rfl

@[simp] theorem targetRowCertificate_matchesView (tg : RootTarget) :
    TargetRowCertificate tg = TargetRowCertificateOfView tg (rootRowView tg) := rfl


theorem targetRowCertificate_of_noRootKind
    (tg : RootTarget)
    (h : rootRowKind tg = .noRootRow) :
    TargetRowCertificate tg = NoRootRow (rootTargetTerm tg) := by
  cases tg <;> simp [TargetRowCertificate, rootTargetTerm, rootRowKind] at h ⊢

theorem targetRowCertificate_of_mixedKind_uHole
    (_h : rootRowKind RootTarget.uHolePred = .mixedRow) :
    TargetRowCertificate RootTarget.uHolePred =
      MixedRootRow
        (SqAbsorbProductiveGoal uHolePredTerm uTerm)
        (SqStableNoRootGoal uHolePredTerm)
        (DecorNoRootGoal uHolePredTerm)
        (C2C1ProductiveGoal uHolePredTerm uTerm) := by
  simp [TargetRowCertificate]

theorem targetRowCertificate_of_mixedKind_uDecorHole
    (_h : rootRowKind RootTarget.uDecorHolePred = .mixedRow) :
    TargetRowCertificate RootTarget.uDecorHolePred =
      MixedRootRow
        (SqAbsorbNoRootGoal uDecorHolePredTerm)
        (SqStableNoRootGoal uDecorHolePredTerm)
        (DecorProductiveGoal uDecorHolePredTerm uTerm)
        (C2C1NoRootGoal uDecorHolePredTerm) := by
  simp [TargetRowCertificate]

abbrev GlobalNoRootWitness {α : Type} {n : Nat}
    (p : Pat n) (target : Term α) : Prop :=
  NoRootInstance p target

abbrev LeftShellNoRootWitness {α : Type} {n : Nat}
    (p : Pat n) (target : Term α) : Prop :=
  NoRootInstance p target

abbrev RightShellNoRootWitness {α : Type} {n : Nat}
    (p : Pat n) (target : Term α) : Prop :=
  NoRootInstance p target

theorem noRootInstance_of_global
    {α : Type} {n : Nat} {p : Pat n} {target : Term α}
    (h : GlobalNoRootWitness p target) :
    NoRootInstance p target := h

theorem noRootInstance_of_leftShell
    {α : Type} {n : Nat} {p : Pat n} {target : Term α}
    (h : LeftShellNoRootWitness p target) :
    NoRootInstance p target := h

theorem noRootInstance_of_rightShell
    {α : Type} {n : Nat} {p : Pat n} {target : Term α}
    (h : RightShellNoRootWitness p target) :
    NoRootInstance p target := h

abbrev SqAbsorbRightForcingWitness {α : Type} (target : Term α) :=
  RightForcingWitness sqAbsorbPat target

abbrev DecorRightForcingWitness {α : Type} (target : Term α) :=
  RightForcingWitness decorPat target

abbrev SqAbsorbGlobalNoRootWitness {α : Type} (target : Term α) :=
  GlobalNoRootWitness sqAbsorbPat target

abbrev SqStableGlobalNoRootWitness {α : Type} (target : Term α) :=
  GlobalNoRootWitness sqStablePat target

abbrev DecorGlobalNoRootWitness {α : Type} (target : Term α) :=
  GlobalNoRootWitness decorPat target

abbrev C2C1GlobalNoRootWitness {α : Type} (target : Term α) :=
  GlobalNoRootWitness c2c1Pat target

abbrev SqAbsorbLeftShellWitness {α : Type} (target : Term α) :=
  LeftShellNoRootWitness sqAbsorbPat target

abbrev SqStableLeftShellWitness {α : Type} (target : Term α) :=
  LeftShellNoRootWitness sqStablePat target

abbrev DecorLeftShellWitness {α : Type} (target : Term α) :=
  LeftShellNoRootWitness decorPat target

abbrev C2C1LeftShellWitness {α : Type} (target : Term α) :=
  LeftShellNoRootWitness c2c1Pat target

abbrev SqAbsorbRightShellWitness {α : Type} (target : Term α) :=
  RightShellNoRootWitness sqAbsorbPat target

abbrev SqStableRightShellWitness {α : Type} (target : Term α) :=
  RightShellNoRootWitness sqStablePat target

abbrev DecorRightShellWitness {α : Type} (target : Term α) :=
  RightShellNoRootWitness decorPat target

abbrev C2C1RightShellWitness {α : Type} (target : Term α) :=
  RightShellNoRootWitness c2c1Pat target

theorem no_sqAbsorb_root_eq_of_rightForcing
    {α : Type} {target : Term α}
    (w : SqAbsorbRightForcingWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target := by
  exact no_sqAbsorb_root_eq_of_no_instance (RightForcingWitness.noRootInstance w)

theorem no_decor_root_eq_of_rightForcing
    {α : Type} {target : Term α}
    (w : DecorRightForcingWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target := by
  exact no_decor_root_eq_of_no_instance (RightForcingWitness.noRootInstance w)

theorem no_sqAbsorb_root_eq_of_globalNoRoot
    {α : Type} {target : Term α}
    (h : SqAbsorbGlobalNoRootWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target := by
  exact no_sqAbsorb_root_eq_of_no_instance (noRootInstance_of_global h)

theorem no_sqStable_root_eq_of_globalNoRoot
    {α : Type} {target : Term α}
    (h : SqStableGlobalNoRootWitness target) :
    ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ target := by
  exact no_sqStable_root_eq_of_no_instance (noRootInstance_of_global h)

theorem no_decor_root_eq_of_globalNoRoot
    {α : Type} {target : Term α}
    (h : DecorGlobalNoRootWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target := by
  exact no_decor_root_eq_of_no_instance (noRootInstance_of_global h)

theorem no_c2c1_root_eq_of_globalNoRoot
    {α : Type} {target : Term α}
    (h : C2C1GlobalNoRootWitness target) :
    ∀ x0 p z0 : Term α, (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ target := by
  exact no_c2c1_root_eq_of_no_instance (noRootInstance_of_global h)

theorem no_sqAbsorb_root_eq_of_leftShell
    {α : Type} {target : Term α}
    (h : SqAbsorbLeftShellWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target := by
  exact no_sqAbsorb_root_eq_of_no_instance (noRootInstance_of_leftShell h)

theorem no_sqStable_root_eq_of_leftShell
    {α : Type} {target : Term α}
    (h : SqStableLeftShellWitness target) :
    ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ target := by
  exact no_sqStable_root_eq_of_no_instance (noRootInstance_of_leftShell h)

theorem no_decor_root_eq_of_leftShell
    {α : Type} {target : Term α}
    (h : DecorLeftShellWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target := by
  exact no_decor_root_eq_of_no_instance (noRootInstance_of_leftShell h)

theorem no_c2c1_root_eq_of_leftShell
    {α : Type} {target : Term α}
    (h : C2C1LeftShellWitness target) :
    ∀ x0 p z0 : Term α, (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ target := by
  exact no_c2c1_root_eq_of_no_instance (noRootInstance_of_leftShell h)

theorem no_sqAbsorb_root_eq_of_rightShell
    {α : Type} {target : Term α}
    (h : SqAbsorbRightShellWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op u)) ≠ target := by
  exact no_sqAbsorb_root_eq_of_no_instance (noRootInstance_of_rightShell h)

theorem no_sqStable_root_eq_of_rightShell
    {α : Type} {target : Term α}
    (h : SqStableRightShellWitness target) :
    ∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ target := by
  exact no_sqStable_root_eq_of_no_instance (noRootInstance_of_rightShell h)

theorem no_decor_root_eq_of_rightShell
    {α : Type} {target : Term α}
    (h : DecorRightShellWitness target) :
    ∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ target := by
  exact no_decor_root_eq_of_no_instance (noRootInstance_of_rightShell h)

theorem no_c2c1_root_eq_of_rightShell
    {α : Type} {target : Term α}
    (h : C2C1RightShellWitness target) :
    ∀ x0 p z0 : Term α, (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ target := by
  exact no_c2c1_root_eq_of_no_instance (noRootInstance_of_rightShell h)

/--
Generic binary plug decomposition:
if `Ctx.plug C r = L ⋆ R`, then the redex sits either at the root,
or somewhere in the left branch, or somewhere in the right branch.
-/
theorem plug_eq_op_cases
    {α : Type}
    (C : Ctx α) (r L R : Term α)
    (h : Ctx.plug C r = L.op R) :
    (C = Ctx.hole ∧ r = L.op R) ∨
    (∃ C', C = Ctx.left C' R ∧ Ctx.plug C' r = L) ∨
    (∃ C', C = Ctx.right L C' ∧ Ctx.plug C' r = R) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C' R' =>
      dsimp [Ctx.plug] at h
      injection h with hL hR
      subst hR
      exact Or.inr (Or.inl ⟨C', rfl, hL⟩)
  | right L' C' =>
      dsimp [Ctx.plug] at h
      injection h with hL hR
      subst hL
      exact Or.inr (Or.inr ⟨C', rfl, hR⟩)

/-- The theorem payload expected for a registered lhs plug-decomposition row. -/
def PlugLhsRowCertificate (tg : PlugMainTarget) : Prop :=
  ∀ (C : Ctx V) (r : Term V), Ctx.plug C r = plugMainTargetTerm tg ->
    (C = Ctx.hole ∧ r = plugMainTargetTerm tg) ∨
    (∃ C', C = Ctx.left C' (plugSubtermTerm (plugLhsRow tg).right) ∧
        Ctx.plug C' r = plugSubtermTerm (plugLhsRow tg).left) ∨
    (∃ C', C = Ctx.right (plugSubtermTerm (plugLhsRow tg).left) C' ∧
        Ctx.plug C' r = plugSubtermTerm (plugLhsRow tg).right)

/-- `PlugLhsRowCertificate` is computed directly from the plug registry view. -/
abbrev PlugLhsRowCertificateOfView (view : PlugLhsRowView) : Prop :=
  PlugLhsRowCertificate view.target

@[simp] theorem plugLhsRowCertificate_matchesView (tg : PlugMainTarget) :
    PlugLhsRowCertificate tg = PlugLhsRowCertificateOfView (plugLhsRowView tg) := rfl

@[simp] theorem plugLhsRowCertificate_xAStablePred :
    PlugLhsRowCertificate PlugMainTarget.xAStablePred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = xAStablePredTerm ->
        (C = Ctx.hole ∧ r = xAStablePredTerm) ∨
        (∃ C', C = Ctx.left C' (A.op x) ∧ Ctx.plug C' r = x) ∨
        (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = A.op x)) := rfl
@[simp] theorem plugLhsRowCertificate_uStablePred :
    PlugLhsRowCertificate PlugMainTarget.uStablePred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uStablePredTerm ->
        (C = Ctx.hole ∧ r = uStablePredTerm) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xAStablePredTerm) ∨
        (∃ C', C = Ctx.right xAStablePredTerm C' ∧ Ctx.plug C' r = s)) := rfl
@[simp] theorem plugLhsRowCertificate_uHolePred :
    PlugLhsRowCertificate PlugMainTarget.uHolePred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uHolePredTerm ->
        (C = Ctx.hole ∧ r = uHolePredTerm) ∨
        (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = uTerm) ∨
        (∃ C', C = Ctx.right uTerm C' ∧ Ctx.plug C' r = A)) := rfl
@[simp] theorem plugLhsRowCertificate_uDecorHolePred :
    PlugLhsRowCertificate PlugMainTarget.uDecorHolePred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uDecorHolePredTerm ->
        (C = Ctx.hole ∧ r = uDecorHolePredTerm) ∨
        (∃ C', C = Ctx.left C' (s.op A) ∧ Ctx.plug C' r = uTerm) ∨
        (∃ C', C = Ctx.right uTerm C' ∧ Ctx.plug C' r = s.op A)) := rfl
@[simp] theorem plugLhsRowCertificate_m :
    PlugLhsRowCertificate PlugMainTarget.m =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = mTerm ->
        (C = Ctx.hole ∧ r = mTerm) ∨
        (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = vTerm) ∨
        (∃ C', C = Ctx.right vTerm C' ∧ Ctx.plug C' r = s.op vTerm)) := rfl
@[simp] theorem plugLhsRowCertificate_uDecorRightPred :
    PlugLhsRowCertificate PlugMainTarget.uDecorRightPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uDecorRightPredTerm ->
        (C = Ctx.hole ∧ r = uDecorRightPredTerm) ∨
        (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = xATerm) ∨
        (∃ C', C = Ctx.right xATerm C' ∧ Ctx.plug C' r = s.op vTerm)) := rfl
@[simp] theorem plugLhsRowCertificate_xASqRightPred :
    PlugLhsRowCertificate PlugMainTarget.xASqRightPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = xASqRightSPredTerm ->
        (C = Ctx.hole ∧ r = xASqRightSPredTerm) ∨
        (∃ C', C = Ctx.left C' (s.op A) ∧ Ctx.plug C' r = x) ∨
        (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = s.op A)) := rfl
@[simp] theorem plugLhsRowCertificate_uSqLiftRightPred :
    PlugLhsRowCertificate PlugMainTarget.uSqLiftRightPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uSqLiftRightSPredTerm ->
        (C = Ctx.hole ∧ r = uSqLiftRightSPredTerm) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xASqRightSPredTerm) ∨
        (∃ C', C = Ctx.right xASqRightSPredTerm C' ∧ Ctx.plug C' r = s)) := rfl
@[simp] theorem plugLhsRowCertificate_xADecorRightPred :
    PlugLhsRowCertificate PlugMainTarget.xADecorRightPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = xADecorRightSPredTerm ->
        (C = Ctx.hole ∧ r = xADecorRightSPredTerm) ∨
        (∃ C', C = Ctx.left C' (s.op (s.op vTerm)) ∧ Ctx.plug C' r = x) ∨
        (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = s.op (s.op vTerm))) := rfl
@[simp] theorem plugLhsRowCertificate_uDecorLiftRightPred :
    PlugLhsRowCertificate PlugMainTarget.uDecorLiftRightPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uDecorLiftRightSPredTerm ->
        (C = Ctx.hole ∧ r = uDecorLiftRightSPredTerm) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xADecorRightSPredTerm) ∨
        (∃ C', C = Ctx.right xADecorRightSPredTerm C' ∧ Ctx.plug C' r = s)) := rfl
@[simp] theorem plugLhsRowCertificate_xASqAPred :
    PlugLhsRowCertificate PlugMainTarget.xASqAPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = xASqAPredTerm ->
        (C = Ctx.hole ∧ r = xASqAPredTerm) ∨
        (∃ C', C = Ctx.left C' (A.op A) ∧ Ctx.plug C' r = x) ∨
        (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = A.op A)) := rfl
@[simp] theorem plugLhsRowCertificate_uSqLiftAPred :
    PlugLhsRowCertificate PlugMainTarget.uSqLiftAPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uSqLiftAPredTerm ->
        (C = Ctx.hole ∧ r = uSqLiftAPredTerm) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xASqAPredTerm) ∨
        (∃ C', C = Ctx.right xASqAPredTerm C' ∧ Ctx.plug C' r = s)) := rfl
@[simp] theorem plugLhsRowCertificate_xADecorLeftPred :
    PlugLhsRowCertificate PlugMainTarget.xADecorLeftPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = xADecorLeftSPredTerm ->
        (C = Ctx.hole ∧ r = xADecorLeftSPredTerm) ∨
        (∃ C', C = Ctx.left C' ((s.op vTerm).op s) ∧ Ctx.plug C' r = x) ∨
        (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = (s.op vTerm).op s)) := rfl
@[simp] theorem plugLhsRowCertificate_uDecorLiftLeftPred :
    PlugLhsRowCertificate PlugMainTarget.uDecorLiftLeftPred =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = uDecorLiftLeftSPredTerm ->
        (C = Ctx.hole ∧ r = uDecorLiftLeftSPredTerm) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xADecorLeftSPredTerm) ∨
        (∃ C', C = Ctx.right xADecorLeftSPredTerm C' ∧ Ctx.plug C' r = s)) := rfl




/-- The theorem payload expected for a registered rhs plug-decomposition row. -/
def PlugRhsRowCertificate (tg : PlugRhsTarget) : Prop :=
  ∀ (C : Ctx V) (r : Term V), Ctx.plug C r = plugRhsTargetTerm tg ->
    (C = Ctx.hole ∧ r = plugRhsTargetTerm tg) ∨
    (∃ C', C = Ctx.left C' (plugSubtermTerm (plugRhsRowView tg).row.right) ∧
        Ctx.plug C' r = plugSubtermTerm (plugRhsRowView tg).row.left) ∨
    (∃ C', C = Ctx.right (plugSubtermTerm (plugRhsRowView tg).row.left) C' ∧
        Ctx.plug C' r = plugSubtermTerm (plugRhsRowView tg).row.right)

/-- `PlugRhsRowCertificate` is computed directly from the plug rhs registry view. -/
abbrev PlugRhsRowCertificateOfView (view : PlugRhsRowView) : Prop :=
  PlugRhsRowCertificate view.target

@[simp] theorem plugRhsRowView_target (tg : PlugRhsTarget) :
    (plugRhsRowView tg).target = tg := by
  cases tg <;> rfl

@[simp] theorem plugRhsRowCertificate_matchesView (tg : PlugRhsTarget) :
    PlugRhsRowCertificate tg = PlugRhsRowCertificateOfView (plugRhsRowView tg) := by
  simp [PlugRhsRowCertificateOfView]

@[simp] theorem plugRhsRowCertificate_sA :
    PlugRhsRowCertificate PlugRhsTarget.sA =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = s.op A ->
        (C = Ctx.hole ∧ r = s.op A) ∨
        (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = s) ∨
        (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = A)) := by rfl

@[simp] theorem plugRhsRowCertificate_sv :
    PlugRhsRowCertificate PlugRhsTarget.sv =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = s.op vTerm ->
        (C = Ctx.hole ∧ r = s.op vTerm) ∨
        (∃ C', C = Ctx.left C' vTerm ∧ Ctx.plug C' r = s) ∨
        (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = vTerm)) := by rfl

@[simp] theorem plugRhsRowCertificate_ssv :
    PlugRhsRowCertificate PlugRhsTarget.ssv =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = s.op (s.op vTerm) ->
        (C = Ctx.hole ∧ r = s.op (s.op vTerm)) ∨
        (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = s) ∨
        (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = s.op vTerm)) := by rfl

@[simp] theorem plugRhsRowCertificate_svs :
    PlugRhsRowCertificate PlugRhsTarget.svs =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = ((s.op vTerm).op s) ->
        (C = Ctx.hole ∧ r = ((s.op vTerm).op s)) ∨
        (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = (s.op vTerm)) ∨
        (∃ C', C = Ctx.right (s.op vTerm) C' ∧ Ctx.plug C' r = s)) := by rfl

@[simp] theorem plugRhsRowCertificate_AA :
    PlugRhsRowCertificate PlugRhsTarget.AA =
      (∀ (C : Ctx V) (r : Term V), Ctx.plug C r = A.op A ->
        (C = Ctx.hole ∧ r = A.op A) ∨
        (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = A) ∨
        (∃ C', C = Ctx.right A C' ∧ Ctx.plug C' r = A)) := by rfl



/-- Per-rule context-step goal: there is no SqAbsorb step from the source normal form. -/
abbrev SqAbsorbCtxNoStepGoal {α : Type} (src : NormalForm α) :=
  ∀ {z : NormalForm α}, ¬ NFSqStepCtx (α := α) src z

/-- Per-rule context-step goal: every SqAbsorb step from the source reaches the fixed target. -/
abbrev SqAbsorbCtxEqGoal {α : Type} (src dst : NormalForm α) :=
  ∀ {z : NormalForm α}, NFSqStepCtx (α := α) src z → z = dst

abbrev SqStableCtxNoStepGoal {α : Type} (src : NormalForm α) :=
  ∀ {z : NormalForm α}, ¬ NFSqStableStepCtx (α := α) src z

abbrev SqStableCtxEqGoal {α : Type} (src dst : NormalForm α) :=
  ∀ {z : NormalForm α}, NFSqStableStepCtx (α := α) src z → z = dst

abbrev DecorCtxNoStepGoal {α : Type} (src : NormalForm α) :=
  ∀ {z : NormalForm α}, ¬ NFDecorStepCtx (α := α) src z

abbrev DecorCtxEqGoal {α : Type} (src dst : NormalForm α) :=
  ∀ {z : NormalForm α}, NFDecorStepCtx (α := α) src z → z = dst

abbrev C2C1CtxNoStepGoal {α : Type} (src : NormalForm α) :=
  ∀ {z : NormalForm α}, ¬ NFC2C1StepCtx (α := α) src z

abbrev C2C1CtxEqGoal {α : Type} (src dst : NormalForm α) :=
  ∀ {z : NormalForm α}, NFC2C1StepCtx (α := α) src z → z = dst



/-- Context-step channel used in finite context profiles. -/
inductive CtxChannel where
  | root
  | left
  | right
deriving DecidableEq, Repr

/-- Named normal-form targets used by the first finite-profile prototypes. -/
inductive CtxNFTag where
  | nfXA
  | nfXASqRightPred
  | nfU
  | nfUSqLiftRightPred
  | nfUHolePred
  | nfM
deriving DecidableEq, Repr

abbrev CtxEdge := CtxChannel × CtxNFTag
abbrev CtxProfile := List CtxEdge

/-- A tagged finite-profile certificate for one context-step cell. -/
structure CtxCellProfileCertificate {α : Type}
    (interp : CtxNFTag -> NormalForm α)
    (Step : NormalForm α -> NormalForm α -> Prop)
    (src : NormalForm α)
    (profile : CtxProfile) : Prop where
  sound : ∀ e, e ∈ profile -> Step src (interp e.2)
  complete : ∀ {z : NormalForm α}, Step src z -> ∃ e, e ∈ profile ∧ z = interp e.2

/--
A purified finite profile remembers that all edges, if any, come from a single channel.
The `channel? = none` case is the empty profile.
-/
structure PurifiedCtxProfile where
  channel? : Option CtxChannel
  tags     : List CtxNFTag
deriving Repr

/-- Expand a purified profile to the tagged edge list used by `CtxCellProfileCertificate`. -/
def PurifiedCtxProfile.toCtxProfile (p : PurifiedCtxProfile) : CtxProfile :=
  match p.channel? with
  | none => []
  | some ch => p.tags.map (fun tag => (ch, tag))

/-- A profile is channel-pure if all edges lie over one fixed channel. -/
def ChannelPure (profile : CtxProfile) : Prop :=
  ∃ ch, ∀ e, e ∈ profile -> e.1 = ch

/-- A channel-pure certificate packaged directly at the purified level. -/
structure PurifiedCtxCellProfileCertificate {α : Type}
    (interp : CtxNFTag -> NormalForm α)
    (Step : NormalForm α -> NormalForm α -> Prop)
    (src : NormalForm α)
    (profile : PurifiedCtxProfile) : Prop where
  cert : CtxCellProfileCertificate interp Step src profile.toCtxProfile
  pure : profile.channel? = none ∨ ∃ ch, profile.channel? = some ch


/-- A purified context-profile row, one purified profile for each R4 rule. -/
structure PurifiedCtxRow where
  sqAbsorb : PurifiedCtxProfile
  sqStable : PurifiedCtxProfile
  decor    : PurifiedCtxProfile
  c2c1     : PurifiedCtxProfile
deriving Repr

/-- Helper: every nonempty purified profile is channel-pure after expansion. -/
theorem purifiedProfile_channelPure (p : PurifiedCtxProfile) :
    p.channel? ≠ none -> ChannelPure p.toCtxProfile := by
  intro hp
  rcases p with ⟨chopt, tags⟩
  cases chopt with
  | none => cases hp rfl
  | some ch =>
      refine ⟨ch, ?_⟩
      intro e he
      simp [PurifiedCtxProfile.toCtxProfile] at he
      rcases he with ⟨t, ht, rfl⟩
      rfl

/-- Every cell of a purified row is channel-pure when nonempty. -/
theorem purifiedCtxRow_channelPure
    (row : PurifiedCtxRow)
    (hsqA : row.sqAbsorb.channel? ≠ none)
    (hsqS : row.sqStable.channel? ≠ none)
    (hdec : row.decor.channel? ≠ none)
    (hc2  : row.c2c1.channel? ≠ none) :
    ChannelPure row.sqAbsorb.toCtxProfile ∧
    ChannelPure row.sqStable.toCtxProfile ∧
    ChannelPure row.decor.toCtxProfile ∧
    ChannelPure row.c2c1.toCtxProfile := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact purifiedProfile_channelPure row.sqAbsorb hsqA
  · exact purifiedProfile_channelPure row.sqStable hsqS
  · exact purifiedProfile_channelPure row.decor hdec
  · exact purifiedProfile_channelPure row.c2c1 hc2


/-- Generic exact certificate for an empty cell. -/
theorem ctxCellProfileCertificate_empty
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (hno : ∀ {z : NormalForm α}, ¬ Step src z) :
    CtxCellProfileCertificate interp Step src [] := by
  refine ⟨?_, ?_⟩
  · intro e he
    cases he
  · intro z hz
    exact False.elim (hno hz)

/-- Generic exact certificate for a singleton cell. -/
theorem ctxCellProfileCertificate_singleton
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (ch : CtxChannel) (tag : CtxNFTag)
    (hsound : Step src (interp tag))
    (hcomplete : ∀ {z : NormalForm α}, Step src z -> z = interp tag) :
    CtxCellProfileCertificate interp Step src [(ch, tag)] := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp at he
    rcases he with rfl
    exact hsound
  · intro z hz
    refine ⟨(ch, tag), by simp, ?_⟩
    exact hcomplete hz

/-- Generic exact certificate for a two-tag same-channel branching cell. -/
theorem ctxCellProfileCertificate_branching₂
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (ch : CtxChannel) (tag₁ tag₂ : CtxNFTag)
    (hsound₁ : Step src (interp tag₁))
    (hsound₂ : Step src (interp tag₂))
    (hcomplete : ∀ {z : NormalForm α}, Step src z -> z = interp tag₁ ∨ z = interp tag₂) :
    CtxCellProfileCertificate interp Step src [(ch, tag₁), (ch, tag₂)] := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp at he
    rcases he with rfl | rfl
    · exact hsound₁
    · exact hsound₂
  · intro z hz
    rcases hcomplete hz with hz₁ | hz₂
    · refine ⟨(ch, tag₁), by simp, hz₁⟩
    · refine ⟨(ch, tag₂), by simp, hz₂⟩

/-- Channel-tag envelope for cells whose codomain is known before exact support is certified. -/
structure CtxCellCodomainEnvelope {α : Type}
    (interp : CtxNFTag -> NormalForm α)
    (Step : NormalForm α -> NormalForm α -> Prop)
    (src : NormalForm α) where
  channel? : Option CtxChannel
  tags     : List CtxNFTag
  complete : ∀ {z : NormalForm α}, Step src z -> z ∈ tags.map interp

/-- Purified exact certificate for an empty cell. -/
theorem purifiedCtxCellProfileCertificate_empty
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (hno : ∀ {z : NormalForm α}, ¬ Step src z) :
    PurifiedCtxCellProfileCertificate interp Step src
      { channel? := none, tags := [] } := by
  refine ⟨ctxCellProfileCertificate_empty hno, Or.inl rfl⟩

/-- Purified exact certificate for a singleton cell. -/
theorem purifiedCtxCellProfileCertificate_singleton
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (ch : CtxChannel) (tag : CtxNFTag)
    (hsound : Step src (interp tag))
    (hcomplete : ∀ {z : NormalForm α}, Step src z -> z = interp tag) :
    PurifiedCtxCellProfileCertificate interp Step src
      { channel? := some ch, tags := [tag] } := by
  refine ⟨ctxCellProfileCertificate_singleton ch tag hsound hcomplete, ?_⟩
  exact Or.inr ⟨ch, rfl⟩

/-- Purified exact certificate for a same-channel two-tag branching cell. -/
theorem purifiedCtxCellProfileCertificate_branching₂
    {α : Type}
    {interp : CtxNFTag -> NormalForm α}
    {Step : NormalForm α -> NormalForm α -> Prop}
    {src : NormalForm α}
    (ch : CtxChannel) (tag₁ tag₂ : CtxNFTag)
    (hsound₁ : Step src (interp tag₁))
    (hsound₂ : Step src (interp tag₂))
    (hcomplete : ∀ {z : NormalForm α}, Step src z -> z = interp tag₁ ∨ z = interp tag₂) :
    PurifiedCtxCellProfileCertificate interp Step src
      { channel? := some ch, tags := [tag₁, tag₂] } := by
  refine ⟨ctxCellProfileCertificate_branching₂ ch tag₁ tag₂ hsound₁ hsound₂ hcomplete, ?_⟩
  exact Or.inr ⟨ch, rfl⟩

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
