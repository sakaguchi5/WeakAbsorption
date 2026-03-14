namespace WeakAbsorption.Classification.Shared

/-- 候補法則の分類状態 -/
inductive CandidateStatus where
  | refuted    -- 反例が見つかった
  | survived   -- 今回の探索範囲では反例なし（まだ証明ではない）
  | provedNew  -- Leanで新規生成元として証明済み
  | derived    -- 既知生成元から導出できる
  | open       -- 未処理
deriving DecidableEq, Repr

end WeakAbsorption.Classification.Shared
