import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption
namespace Proof

variable {α : Type}

-- C1 が root で打てるなら、実際に RedStep が 1歩出る（しかも結果は左項 t）
theorem IsC1Root.to_RedStep {t u : Term α} (h : IsC1Root (α := α) t u) :
  RedStep (Term.op t u) t := by
  rcases h with ⟨x, rfl⟩
  -- goal: RedStep (((x⋆u)⋆u)) (x⋆u)
  simpa using (RedStep.C1 (α := α) x u)

-- 「C1 が root で適用できる形」 ↔ 「(x を伴って) C1 の RedStep が root で成立する形」
theorem IsC1Root_iff_root_C1 {t u : Term α} :
  IsC1Root (α := α) t u ↔ ∃ x, RedStep (Term.op t u) t ∧ t = Term.op x u := by
  constructor
  · intro h
    rcases h with ⟨x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simpa using (RedStep.C1 (α := α) x u)
  · rintro ⟨x, _hs, hx⟩
    exact ⟨x, hx⟩

-- C2' が root で打てるなら、実際に RedStep が 1歩出る（しかも結果は左項 t）
theorem IsC2pRoot.to_RedStep {t u : Term α} (h : IsC2pRoot (α := α) t u) :
  RedStep (Term.op t u) t := by
  cases u with
  | var a =>
      cases h
  | op y z =>
      dsimp [IsC2pRoot] at h
      rcases h with ⟨x, rfl⟩
      -- goal: RedStep ((((x⋆y)⋆z)⋆(y⋆z))) ((x⋆y)⋆z)
      simpa using (RedStep.C2p (α := α) x y z)

-- 「C2' が root で適用できる形」 ↔ 「(x,y,z を伴って) C2' の RedStep が root で成立する形」
theorem IsC2pRoot_iff_root_C2p {t u : Term α} :
  IsC2pRoot (α := α) t u
    ↔ ∃ x y z, u = Term.op y z
        ∧ t = Term.op (Term.op x y) z
        ∧ RedStep (Term.op t u) t := by
  constructor
  · intro h
    cases u with
    | var a =>
        cases h
    | op y z =>
        dsimp [IsC2pRoot] at h
        rcases h with ⟨x, rfl⟩
        refine ⟨x, y, z, rfl, rfl, ?_⟩
        simpa using (RedStep.C2p (α := α) x y z)
  · rintro ⟨x, y, z, rfl, rfl, _hs⟩
    -- goal: IsC2pRoot ((x⋆y)⋆z) (y⋆z)
    dsimp [IsC2pRoot]
    exact ⟨x, rfl⟩

-- （おまけ）root で「左項に落ちる RedStep」があるのは C1 か C2' のどちらか、まで 1本で言える
theorem RedStep_root_to_left_iff {t u : Term α} :
  RedStep (Term.op t u) t ↔ IsC1Root (α := α) t u ∨ IsC2pRoot (α := α) t u := by
  constructor
  · intro hs
    cases hs with
    | C1 x y =>
        exact Or.inl ⟨x, rfl⟩
    | C2p x y z =>
        exact Or.inr (by
          dsimp [IsC2pRoot]
          exact ⟨x, rfl⟩)
  · intro h
    cases h with
    | inl hc1 => exact IsC1Root.to_RedStep (α := α) hc1
    | inr hc2 => exact IsC2pRoot.to_RedStep (α := α) hc2

end Proof
end WeakAbsorption
