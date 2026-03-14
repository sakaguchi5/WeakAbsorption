import WeakAbsorption.Proof.Generators.Vars1.Complete.Step6
--import WeakAbsorption.Tooling.SmallCheck.Phase0

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step7

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step6

/-!
Step7: Completion wrapper for vars=1 (after Step6).

After Step6, the “complete vars=1 story” reduces to one bridge:

    GapTermAt R K u v  →  Vars1OrbitTpl u v

If you have that bridge, then:
- every raw gap has canonical core (coreU/coreV at fuel = size u + size v) in Vars1CoreTpl,
- hence every raw gap belongs to one of two kernel kinds (SqAbsorb vs SqStable),
- and Step8 is exposed as the only remaining hard obligation.
-/

section

-- ============================================================
-- 7.1  Small facts used to discharge `if`-conditions in getCoreKind?
-- ============================================================

theorem Au_ne_s : Au ≠ s := by
  intro h
  have hs : size Au = size s := congrArg size h
  -- Step1 の size_Au=9, size_s=3 を使う
  simp [size_Au, size_s] at hs

theorem cond_false_for_Au_A :
  ¬ ((Au = A ∧ A = s) ∨ (Au = s)) := by
  intro h
  cases h with
  | inl h1 =>
      -- Au = A で矛盾
      exact Au_ne_A h1.1
  | inr h2 =>
      exact Au_ne_s h2

theorem cond_false_for_A_Au :
  ¬ ((A = A ∧ Au = s) ∨ (A = s ∧ Au = A)) := by
  intro h
  cases h with
  | inl h1 =>
      -- A=A は真なので Au=s に帰着
      exact Au_ne_s h1.2
  | inr h2 =>
      -- A=s で矛盾
      exact A_ne_s h2.1

-- ============================================================
-- 7.2  Core kind (data) + safe classifier (Option)
-- ============================================================

-- Kind is data (Type), not Prop: usable for later computation / logging / case-splits.
inductive Vars1CoreKind : Type
  | sqAbsorb
  | sqStable
  deriving DecidableEq, Repr

/--
Classify a pair if it is one of the finite vars=1 core templates; otherwise `none`.

- sqAbsorb-kernel: (A,s) or (s,A)
- sqStable-kernel: (Au,A) or (A,Au)
-/
def getCoreKind? (u v : Term V) : Option Vars1CoreKind :=
  if (u = A && v = s) || (u = s && v = A) then
    some .sqAbsorb
  else if (u = Au && v = A) || (u = A && v = Au) then
    some .sqStable
  else
    none

-- ============================================================
-- 7.3  Soundness / completeness of the classifier w.r.t. Vars1CoreTpl
-- ============================================================

/-- If a pair is in Vars1CoreTpl, `getCoreKind?` is not none. -/
theorem getCoreKind?_of_coreTpl {u v : Term V} :
  Vars1CoreTpl u v → getCoreKind? u v ≠ none := by
  intro h
  rcases h with h | h | h | h
  · -- (A,s)
    rcases h with ⟨hu, hv⟩; subst hu; subst hv
    simp [getCoreKind?]
  · -- (s,A)
    rcases h with ⟨hu, hv⟩; subst hu; subst hv
    simp [getCoreKind?]
  · -- (Au,A)
    rcases h with ⟨hu, hv⟩; subst hu; subst hv
    have hcond : ¬ ((Au = A ∧ A = s) ∨ (Au = s)) := cond_false_for_Au_A
    -- if の条件が false なので else = some sqStable、よって ≠ none
    simp [getCoreKind?, hcond]
  · -- (A,Au)
    rcases h with ⟨hu, hv⟩; subst hu; subst hv
    -- ここは `simp` だけでは分岐が残りやすいので split で確実に閉じる
    simp [getCoreKind?]
    split
    · simp
    · simp

/-- If Vars1CoreTpl holds, `getCoreKind?` returns the corresponding concrete kind value. -/
theorem getCoreKind?_value_of_coreTpl {u v : Term V} :
  Vars1CoreTpl u v →
    getCoreKind? u v = some .sqAbsorb ∨ getCoreKind? u v = some .sqStable := by
  intro h
  have hn : getCoreKind? u v ≠ none := getCoreKind?_of_coreTpl (u := u) (v := v) h
  -- only two some-cases are possible by definition
  -- we do a case split using the concrete equalities provided by Vars1CoreTpl
  rcases h with h | h | h | h
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv
    left; simp [getCoreKind?]
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv
    left; simp [getCoreKind?]
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv
    right
    have hcond : ¬ ((Au = A ∧ A = s) ∨ (Au = s)) := cond_false_for_Au_A
    simp [getCoreKind?, hcond]
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv
    right
    have hcond : ¬ ((A = A ∧ Au = s) ∨ (A = s ∧ Au = A)) := cond_false_for_A_Au
    -- simp に hcond をそのまま渡すのではなく、基本否定（A_ne_s, Au_ne_s, Au_ne_A）で閉じる
    simp [getCoreKind?, A_ne_s, Au_ne_s, Au_ne_A]

/--
Completeness direction:
if the classifier returns `some k`, then the pair is indeed in Vars1CoreTpl.
-/
theorem of_getCoreKind? {u v : Term V} {k : Vars1CoreKind} :
  getCoreKind? u v = some k → Vars1CoreTpl u v := by
  intro h
  -- unfold and analyze the nested if-then-else structure
  unfold getCoreKind? at h
  split at h
  · -- Case 1: (u = A && v = s) || (u = s && v = A) is true
    simp at h
    rename_i hcond
    replace hcond := (Bool.or_eq_true _ _).mp hcond
    rcases hcond with h1 | h2
    · -- u = A, v = s
      simp [Bool.and_eq_true] at h1
      left; exact h1
    · -- u = s, v = A
      simp [Bool.and_eq_true] at h2
      right; left; exact h2
  · -- Case 2: first if is false; analyze the second if
    split at h
    · rename_i hcond
      replace hcond := (Bool.or_eq_true _ _).mp hcond
      rcases hcond with h1 | h2
      · -- u = Au, v = A
        simp [Bool.and_eq_true] at h1
        right; right; left; exact h1
      · -- u = A, v = Au
        simp [Bool.and_eq_true] at h2
        right; right; right; exact h2
    · -- Case 3: both ifs are false, but we have (none = some k)
      contradiction

-- ============================================================
-- 7.4  Completion consequences (assuming gap ⇒ orbit)
-- ============================================================

/-- Step8 obligation packaged as a named predicate. -/
def GapImpliesOrbitAt (R : RuleSet) (K : Nat) : Prop :=
  ∀ u v : Term V, GapTermAt (R := R) K u v → Vars1OrbitTpl u v

/--
Main completion theorem (canonical form):

If raw gaps imply orbit for (R,K), then every raw gap instance has canonical core in Vars1CoreTpl.
-/
theorem GapCoreTplAt_of_GapImpliesOrbitAt
  (R : RuleSet) (K : Nat)
  (h : GapImpliesOrbitAt (R := R) K) :
  GapCoreTplAt (R := R) K :=
by
  exact GapCoreTplAt_of_gapImpliesOrbit (R := R) (K := K) h

/--
Kernel-kind corollary:

Under gap⇒orbit, every raw gap’s canonical core is classifiable (not none).
-/
theorem GapCoreKindClassifiableAt
  (R : RuleSet) (K : Nat)
  (h : GapImpliesOrbitAt (R := R) K) :
  ∀ u v : Term V, GapTermAt (R := R) K u v →
    getCoreKind? (coreU u v) (coreV u v) ≠ none :=
by
  intro u v hGap
  have hTpl : Vars1CoreTpl (coreU u v) (coreV u v) :=
    (GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K) h) u v hGap
  exact getCoreKind?_of_coreTpl (u := coreU u v) (v := coreV u v) hTpl

/--
Even stronger: under gap⇒orbit, every raw gap’s canonical core has a concrete kind value.
-/
theorem GapCoreKindValueAt
  (R : RuleSet) (K : Nat)
  (h : GapImpliesOrbitAt (R := R) K) :
  ∀ u v : Term V, GapTermAt (R := R) K u v →
    (getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
    ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable) :=
by
  intro u v hGap
  have hTpl : Vars1CoreTpl (coreU u v) (coreV u v) :=
    (GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K) h) u v hGap
  exact getCoreKind?_value_of_coreTpl (u := coreU u v) (v := coreV u v) hTpl

/-
-- 手順0を一括実行する
#eval let K := 15
      -- 分析対象の生成ルールを制限（例：空のリストにすると全てのRed接続がギャップになる）
      let R : RuleSet := []

      match findGapWithRedPathAfterNFGen K 0 R with
      | none => "Step 0-1: ギャップは見つかりませんでした（現在の設定では全て接続済みです）"
      | some (u, v, _p) =>
          -- Step 0-2: coreを抽出
          let (_ctx, coreU, coreV) := stripCommonCtxAll u v

          -- Step 0-3 & 0-4: テンプレ判定
          match getCoreKind? coreU coreV with
          | some kind =>
              s!"判定：some ({repr kind})\n" ++
              s!"u: {termStr u}\nv: {termStr v}\n" ++
              s!"coreU: {termStr coreU}\ncoreV: {termStr coreV}"
          | none =>
              s!"判定：none (新しいテンプレが必要です)\n" ++
              s!"coreU: {termStr coreU}\ncoreV: {termStr coreV}"
-/
/-結果
"判定：some (WeakAbsorption.Proof.Generators.Vars1.Complete.Step7.Vars1CoreKind.sqAbsorb)\nu: (x⋆x)\nv: ((x⋆x)⋆(x⋆x))\ncoreU: (x⋆x)\ncoreV: ((x⋆x)⋆(x⋆x))"
-/
/-
/-
seed を 0..(N-1) で回して、見つかった gap の coreKind? を集計する。
none が出たら即停止して、その例を表示する。
-/
def scanGapKinds_tooling (K N : Nat) (R : RuleSet) : String :=
  let rec go (i : Nat) (cntAbs cntStb cntNone : Nat) : String :=
    if _G_genh : i < N then
      match findGapWithRedPathAfterNFGen K i R with
      | none =>
          go (i+1) cntAbs cntStb cntNone
      | some (u, v, _p) =>
          let (_ctx, cu, cv) := stripCommonCtxAll u v
          match getCoreKind? cu cv with
          | some .sqAbsorb =>
              go (i+1) (cntAbs+1) cntStb cntNone
          | some .sqStable =>
              go (i+1) cntAbs (cntStb+1) cntNone
          | none =>
              s!"FOUND NONE\nseed={i}\nR={repr R}\n" ++
              s!"u={termStr u}\nv={termStr v}\n" ++
              s!"coreU={termStr cu}\ncoreV={termStr cv}\n"
    else
      s!"DONE\nR={repr R}\nK={K}, N={N}\n" ++
      s!"sqAbsorb={cntAbs}, sqStable={cntStb}, none={cntNone}"
  go 0 0 0 0


-/
--#eval scanGapKinds_tooling 15 50 ([] : RuleSet)
--結果"FOUND NONE\nseed=1\nR=[]\nu=(x⋆x)\nv=((x⋆x)⋆(x⋆(x⋆x)))\ncoreU=(x⋆x)\ncoreV=((x⋆x)⋆(x⋆(x⋆x)))\n"
--#eval scanGapKinds_tooling_fast 15 50 ([RuleId.SqAbsorb] : RuleSet)
--結果"FOUND NONE\nseed=0\nR=[WeakAbsorption.Spec.RuleId.SqAbsorb]\nu=(x⋆x)\nv=((x⋆x)⋆(x⋆(x⋆x)))\ncoreU=(x⋆x)\ncoreV=((x⋆x)⋆(x⋆(x⋆x)))\n"

end

end Step7
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
