/-
WeakAbsorption/Logic/QuotRelTransport.lean

Quotient equality via lifted relation transport (core-only).

This module provides a reusable pattern:

  1) Lift a relation R : α → α → Prop to Quot R × Quot R → Prop
     using only Quot.lift (nested), not Quot.lift₂.
  2) Use equality transport on the lifted relation to prove “completeness”:

       Quot.mk R a = Quot.mk R b → R a b

The lift is well-defined assuming R is symmetric + transitive.
The completeness step additionally needs reflexivity.
-/

namespace WeakAbsorption.Logic.QuotRelTransport

universe u
variable {α : Type u}

/-- Left well-definedness for lifting R itself: if R a₁ a₂ then (R a₁ b) = (R a₂ b). -/
private theorem wd_left
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  {a₁ a₂ : α} (ha : R a₁ a₂) (b : α) :
  R a₁ b = R a₂ b :=
by
  apply propext
  constructor
  · intro h
    exact trans (symm ha) h
  · intro h
    exact trans ha h

/-- Right well-definedness for lifting R itself: if R b₁ b₂ then (R a b₁) = (R a b₂). -/
private theorem wd_right
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  {b₁ b₂ : α} (hb : R b₁ b₂) (a : α) :
  R a b₁ = R a b₂ :=
by
  apply propext
  constructor
  · intro h
    exact trans h hb
  · intro h
    exact trans h (symm hb)

/-
liftRel: lift R to Quot R × Quot R → Prop (core-only)

Implementation: Quot.lift (outer) returning a function (Quot R → Prop),
then another Quot.lift (inner). The outer well-definedness becomes funext,
and inside that we use Quot.inductionOn to reduce to representatives.
-/
def liftRel
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c) :
  Quot R → Quot R → Prop :=
  Quot.lift
    (fun a : α =>
      Quot.lift
        (fun b : α => R a b)
        (fun b₁ b₂ hb => wd_right (α := α) R symm trans hb a)
    )
    (fun a₁ a₂ ha =>
      funext (fun q =>
        Quot.inductionOn q (fun b : α => by
          simpa using wd_left (α := α) R symm trans ha b
        )
      )
    )

@[simp] theorem liftRel_mk
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  (a b : α) :
  liftRel (α := α) R symm trans (Quot.mk R a) (Quot.mk R b) = R a b :=
rfl

/-- Reflexivity of liftRel follows from reflexivity of R. -/
theorem liftRel_refl
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  (refl : ∀ a, R a a)
  (q : Quot R) :
  liftRel (α := α) R symm trans q q :=
by
  refine Quot.inductionOn q (fun a => ?_)
  -- reduce to representatives
  simp [liftRel_mk, refl]

/-- Equality transport: if q₁ = q₂ then liftRel q₁ q₂, assuming reflexivity of R. -/
theorem liftRel_of_eq
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  (refl : ∀ a, R a a)
  {q₁ q₂ : Quot R} (h : q₁ = q₂) :
  liftRel (α := α) R symm trans q₁ q₂ :=
by
  cases h
  exact liftRel_refl (α := α) R symm trans refl q₁

/-
MAIN TEMPLATE (“completeness via transport”)

Quot.mk R a = Quot.mk R b → R a b

Proof strategy:
  R a b
    = liftRel (mk a) (mk b)
    -- transport equality
    = liftRel (mk b) (mk b)
    = R b b
-/
theorem complete_of_eq
  (R : α → α → Prop)
  (symm : ∀ {a b}, R a b → R b a)
  (trans : ∀ {a b c}, R a b → R b c → R a c)
  (refl : ∀ a, R a a)
  {a b : α} (h : Quot.mk R a = Quot.mk R b) :
  R a b :=
by
  -- move goal into lifted relation
  rw [← liftRel_mk (α := α) R symm trans a b]
  -- transport equality
  rw [h]
  -- reflexive case
  simp [liftRel_mk, refl]

end WeakAbsorption.Logic.QuotRelTransport

/-
Quotient equality via lifted relation transport (core-only, transport formulation)

This module implements a transport-based proof of quotient completeness
using only core primitives (Quot.mk, Quot.lift, equality transport).

GOAL

  Given a relation R : α → α → Prop,
  prove the standard completeness property:

    Quot.mk R a = Quot.mk R b  →  R a b

without using Quot.eq or EqvGen extraction.

CORE IDEA

Instead of unpacking quotient equality to recover a witness in R,
we transport the goal into a lifted relation defined on the quotient itself.

--------------------------------------------------------------------

STEP 1 — Lift the relation to the quotient

We construct:

  liftRel : Quot R → Quot R → Prop

such that:

  liftRel (Quot.mk R a) (Quot.mk R b)  ≡  R a b

This is done using nested Quot.lift only.

Requirements:

  symm  : symmetry of R
  trans : transitivity of R

These ensure well-definedness of the lift.

--------------------------------------------------------------------

STEP 2 — Equality transport inside the lifted relation

Equality in Lean supports transport:

  if q₁ = q₂, then any property of q₁ can be transported to q₂.

Applying this to liftRel gives:

  q₁ = q₂  →  liftRel q₁ q₂

This step requires reflexivity of R,
since transport reduces to liftRel q q, which corresponds to R a a.

--------------------------------------------------------------------

STEP 3 — Completeness proof via transport

Goal:

  R a b

Transport sequence:

  R a b
    ≡ liftRel (Quot.mk R a) (Quot.mk R b)
    → transport equality h : Quot.mk R a = Quot.mk R b
    → liftRel (Quot.mk R b) (Quot.mk R b)
    ≡ R b b
    → reflexivity of R
    → done

No extraction from quotient is required.

--------------------------------------------------------------------

CONCEPTUAL INTERPRETATION

Standard method (Quot.eq):

  quotient equality
    → extract equivalence proof
    → collapse equivalence closure
    → recover R

Transport method (this module):

  quotient equality
    → transport lifted relation
    → reduce to reflexivity
    → recover R

This avoids EqvGen entirely and uses only equality transport.

--------------------------------------------------------------------

WHY THIS IS IMPORTANT

This formulation:

  • uses only core quotient primitives
  • avoids closure extraction
  • exposes quotient completeness as a pure transport phenomenon
  • aligns directly with Lean kernel equality semantics

This is the canonical kernel-level perspective of quotient completeness.
-/

/-
Quotient の等式から relation を復元する：transport（輸送）による証明
（Lean core のみ、Quot.eq や EqvGen を使わない方法）

目的
────────────────────────────────

relation R : α → α → Prop に対して、次を証明する：

  Quot.mk R a = Quot.mk R b  →  R a b

これは quotient completeness（完全性）と呼ばれる基本性質である。

通常は Lean core の primitive：

  Quot.eq :
    Quot.mk R a = Quot.mk R b → EqvGen R a b

を使って証明する。

しかしここでは Quot.eq を一切使わず、
純粋に equality transport（等式による輸送）のみで証明する。

────────────────────────────────
核心アイデア
────────────────────────────────

relation R を quotient 上に lift した relation：

  liftRel : Quot R → Quot R → Prop

を構成する。

この liftRel は次の性質を持つ：

  liftRel (Quot.mk R a) (Quot.mk R b)  ≡  R a b

つまり liftRel は quotient 上の relation だが、
代表元に戻すと元の relation と完全に一致する。

────────────────────────────────
ステップ1：relation を quotient 上に lift する
────────────────────────────────

nested Quot.lift を使って：

  liftRel : Quot R → Quot R → Prop

を構成する。

これは次の意味を持つ：

  quotient 上の2点が liftRel で関係する
    ⇔
  その代表元が R で関係する

well-definedness のために必要：

  trans : 推移性
  symm  : 対称性

────────────────────────────────
ステップ2：等式による relation の transport
────────────────────────────────

Lean の等式は transport を許す：

  q₁ = q₂ のとき、
  q₁ についての性質を q₂ に移すことができる

したがって：

  q₁ = q₂
    → liftRel q₁ q₂

が成立する。

これは reflexivity：

  R a a

に対応する。

────────────────────────────────
ステップ3：completeness 証明の実体
────────────────────────────────

Goal：

  R a b

これを直接証明する代わりに、次のように変形する：

  R a b
    ≡ liftRel (Quot.mk R a) (Quot.mk R b)

ここで equality：

  h : Quot.mk R a = Quot.mk R b

を transport すると：

  liftRel (Quot.mk R b) (Quot.mk R b)

になる。

これは定義より：

  R b b

に等しい。

reflexivity により：

  R b b は成立

したがって：

  R a b が成立する。

────────────────────────────────
重要な概念的意味
────────────────────────────────

通常の方法（Quot.eq）：

  quotient equality
    → relation closure（EqvGen）を取り出す
    → closure を collapse する
    → 元の relation を得る

transport 方法（ここでの方法）：

  quotient equality
    → lifted relation を transport
    → reflexivity に collapse
    → 元の relation を得る

closure extraction は不要。

純粋に transport のみで成立する。

────────────────────────────────
本質的意味（Lean kernel 観点）
────────────────────────────────

quotient equality は：

  relation の証拠を内部に保持しているのではない。

そうではなく：

  relation を transport できる構造

を持っている。

relation の復元は：

  extraction ではなく transport によって起こる。

────────────────────────────────
なぜ重要か
────────────────────────────────

この方法は：

• Lean core primitives のみ使用
• EqvGen 不要
• Quot.eq 不要
• closure collapse 不要

つまり：

Lean kernel の quotient の本質と完全に一致している。

これは quotient completeness の最も純粋な証明形式である。
-/
