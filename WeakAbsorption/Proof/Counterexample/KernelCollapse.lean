import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Equational
import WeakAbsorption.Proof.Generators.SqStableRecheck

namespace WeakAbsorption
namespace Proof
namespace KernelCollapse

open WeakAbsorption.Closure
open WAA

section
variable {α : Type} (a : α)

private def X : Term α := Term.var a
private def S : Term α := (X (α := α) (a := a)) ⋆ (X (a := a))
private def A : Term α := (S (α := α) (a := a)) ⋆ (S (a := a))

-- var は Normal
private theorem X_normal : Normal (X (α := α) (a := a)) := by
  intro u hu
  cases hu with
  | step _ _ hs => cases hs

-- S = x⋆x の root 非発火（C1）
private theorem not_C1_X_X :
  ¬ IsC1Root (α := α) (X (α := α) (a := a)) (X (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  dsimp [X] at hw
  cases hw

-- S = x⋆x の root 非発火（C2p）：u が var なので定義的に False
private theorem not_C2_X_X :
  ¬ IsC2pRoot (α := α) (X (α := α) (a := a)) (X (a := a)) := by
  simp [IsC2pRoot, X]

-- S は Normal
private theorem S_normal : Normal (S (α := α) (a := a)) := by
  have : Normal (α := α) ((X (a := a)) ⋆ (X (a := a))) :=
    (Normal_op_iff (α := α) (X (a := a)) (X (a := a))).2
      ⟨X_normal (α := α) (a := a),
       X_normal (α := α) (a := a),
       not_C1_X_X (α := α) (a := a),
       not_C2_X_X (α := α) (a := a)⟩
  simpa [S] using this

-- A = s⋆s の root 非発火（C1）：s = w⋆s を強制して var=op 矛盾
private theorem not_C1_S_S :
  ¬ IsC1Root (α := α) (S (α := α) (a := a)) (S (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  dsimp [S, X] at hw
  injection hw with h1 h2
  -- h2 : (Term.var a) = (Term.op (Term.var a) (Term.var a))
  cases h2

-- A = s⋆s の root 非発火（C2p）：s = ((w⋆x)⋆x) を強制して var=op 矛盾
private theorem not_C2_S_S :
  ¬ IsC2pRoot (α := α) (S (α := α) (a := a)) (S (a := a)) := by
  intro h
  dsimp [IsC2pRoot, S, X] at h
  rcases h with ⟨w, hw⟩
  injection hw with h1 h2
  -- h1 : (Term.var a) = (Term.op w (Term.var a))
  cases h1

-- A は Normal
private theorem A_normal : Normal (A (α := α) (a := a)) := by
  have : Normal (α := α) ((S (a := a)) ⋆ (S (a := a))) :=
    (Normal_op_iff (α := α) (S (a := a)) (S (a := a))).2
      ⟨S_normal (α := α) (a := a),
       S_normal (α := α) (a := a),
       not_C1_S_S (α := α) (a := a),
       not_C2_S_S (α := α) (a := a)⟩
  simpa [A] using this

/--
(1) **NormalForm 側の“潰れ”**：
vars=1 の最初の非自明核として
  A := (x⋆x)⋆(x⋆x),  s := x⋆x
は **別の NormalForm** だが **NFRel で同値**。
-/
theorem distinct_normalForms_same_kernel (a : α) :
  ∃ p q : NormalForm α, p ≠ q ∧ NFRel (α := α) p q := by
  let p : NormalForm α := ⟨A (α := α) (a := a), A_normal (α := α) (a := a)⟩
  let q : NormalForm α := ⟨S (α := α) (a := a), S_normal (α := α) (a := a)⟩
  refine ⟨p, q, ?_, ?_⟩
  · intro h
    have hval :
        (A (α := α) (a := a)) = (S (α := α) (a := a)) :=
      congrArg (fun r : NormalForm α => r.1) h
    dsimp [A, S, X] at hval
    injection hval with h1 h2
    cases h1
  · -- NFRel p q は RedEq p.1 q.1（定義展開して既存の核補題を当てる）
    dsimp [NFRel, p, q, A, S]
    --dsimp [S]
    exact RedEq_squareSquare_eq_square (α := α) (u := X (α := α) (a := a))

/--
(2) **“商で潰れる” を明示**：
Quot(@RedEq) 上では p と q が同一点になる。
-/
theorem quotient_collapses_distinct_normals (a : α) :
  ∃ (p q : NormalForm α),
    p ≠ q ∧ (Quot.mk (@RedEq α) p.1) = Quot.mk (@RedEq α) q.1 := by
  rcases distinct_normalForms_same_kernel (α := α) (a := a) with ⟨p, q, hpq, hrel⟩
  refine ⟨p, q, hpq, ?_⟩
  have hRedEq : RedEq (α := α) p.1 q.1 := by
    dsimp [NFRel] at hrel
    exact hrel
  exact Quot.sound hRedEq

/--
vars=1 の “核が少数に落ちる” の実体（最初の一撃）：
A⋆x も結局 x⋆x と同じ class に落ちる（右に付け足しても核が変わらない）。
-/
theorem vars1_kernel_right_stable (a : α) :
  RedEq (α := α) ((A (α := α) (a := a)) ⋆ (X (α := α) (a := a)))
                (S (α := α) (a := a)) := by
  dsimp [A, S, X]
  exact RedEq_Au_eq_square (α := α) (u := Term.var a)

/--
(3) **NFQuot 側でも潰れる**：
異なる NormalForm p≠q が、NFQuot では同一点になる。

証明は
  p≠q かつ NFRel p q
  ⇒ proj p.term = proj q.term（WAA 側）
  ⇒ toNFQuot をかけて simp（toNFQuot_fromNFQuot）で NFQuot の等式
という流れ。
-/
theorem distinct_normalForms_same_NFQuot (a : α) :
  ∃ p q : NormalForm α,
    p ≠ q ∧ (Quot.mk (@NFRel α) p : NFQuot α) = Quot.mk (@NFRel α) q := by
  rcases distinct_normalForms_same_kernel (α := α) (a := a) with ⟨p, q, hpq, hrel⟩
  refine ⟨p, q, hpq, ?_⟩

  -- hrel : NFRel p q = RedEq p.1 q.1
  have hRedEq : RedEq (α := α) p.1 q.1 := by
    simpa [NFRel] using hrel

  -- WAA（Quot RedEq）側では同一点：proj p.1 = proj q.1
  have hproj : WAA.proj (α := α) p.1 = WAA.proj (α := α) q.1 :=
    Quot.sound hRedEq

  -- fromNFQuot (mk p) = proj p.1 を使って、NFQuot の2点の像が WAA で等しいことへ
  have hWAA :
      WAA.fromNFQuot (α := α) (Quot.mk (@NFRel α) p)
        = WAA.fromNFQuot (α := α) (Quot.mk (@NFRel α) q) := by
    -- fromNFQuot は Quot.lift なので mk に対しては定義展開で proj に落ちる
    -- （ここで simp は unfold をしてくれないので dsimp で落とす）
    dsimp [WAA.fromNFQuot]  -- 両辺が proj p.1 / proj q.1 になる
    exact hproj

  -- toNFQuot をかけて、simp で mk の等式に戻す
  have hNF : WAA.toNFQuot (α := α) (WAA.fromNFQuot (α := α) (Quot.mk (@NFRel α) p))
            = WAA.toNFQuot (α := α) (WAA.fromNFQuot (α := α) (Quot.mk (@NFRel α) q)) :=
    congrArg (WAA.toNFQuot (α := α)) hWAA

  -- ここが「simp だけで閉じる」ポイント
  simp [WAA.toNFQuot_fromNFQuot] at hNF
  exact hNF

section CanonicalAPI
variable {α : Type}

-- toNFQuot : WAA α → NFQuot α は単射
theorem toNFQuot_injective :
  Function.Injective (WAA.toNFQuot (α := α)) := by
  intro x y h
  have h' := congrArg (WAA.fromNFQuot (α := α)) h
  -- fromNFQuot (toNFQuot x) = x を使って落とす
  simpa [WAA.fromNFQuot_toNFQuot] using h'

-- fromNFQuot : NFQuot α → WAA α は単射
theorem fromNFQuot_injective :
  Function.Injective (WAA.fromNFQuot (α := α)) := by
  intro p q h
  have h' := congrArg (WAA.toNFQuot (α := α)) h
  simpa [WAA.toNFQuot_fromNFQuot] using h'

-- toNFQuot は全射（右逆がある）
theorem toNFQuot_surjective :
  Function.Surjective (WAA.toNFQuot (α := α)) := by
  intro q
  refine ⟨WAA.fromNFQuot (α := α) q, ?_⟩
  simp [WAA.toNFQuot_fromNFQuot]

-- fromNFQuot は全射（左逆がある）
theorem fromNFQuot_surjective :
  Function.Surjective (WAA.fromNFQuot (α := α)) := by
  intro x
  refine ⟨WAA.toNFQuot (α := α) x, ?_⟩
  simp [WAA.fromNFQuot_toNFQuot]

end CanonicalAPI

/-- `Quot.mk (@NFRel α)` は単射ではない：異なる NormalForm が同じ NFQuot 点になる。 -/
theorem mk_NFQuot_not_injective (a : α) :
  ¬ Function.Injective (fun p : NormalForm α => (Quot.mk (@NFRel α) p : NFQuot α)) := by
  intro hinj
  rcases distinct_normalForms_same_NFQuot (α := α) (a := a) with ⟨p, q, hpq, heq⟩
  have : p = q := hinj heq
  exact hpq this

/-- WAA の各元に「唯一の NormalForm 代表」がある、は偽。 -/
theorem not_exists_unique_normal_rep (a : α) :
  ¬ (∀ x : WAA α,
      ∃ p : NormalForm α,
        WAA.proj (α := α) p.1 = x ∧
        ∀ q : NormalForm α,
          WAA.proj (α := α) q.1 = x → q = p) := by
  intro huniq
  rcases distinct_normalForms_same_kernel (α := α) (a := a)
    with ⟨p, q, hpq, hrel⟩

  let x : WAA α := WAA.proj (α := α) p.1

  have hxq : WAA.proj (α := α) q.1 = x := by
    have : WAA.proj (α := α) p.1 =
           WAA.proj (α := α) q.1 :=
      Quot.sound (by simpa [NFRel] using hrel)
    simpa [x] using this.symm

  rcases huniq x with ⟨r, hr₁, hunique⟩

  have pr : p = r := hunique p rfl
  have qr : q = r := hunique q hxq

  exact hpq (pr.trans qr.symm)


end
end KernelCollapse
end Proof
end WeakAbsorption
