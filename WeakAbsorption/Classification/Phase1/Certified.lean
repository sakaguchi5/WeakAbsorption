import WeakAbsorption.Spec.Signatures
import WeakAbsorption.Classification.Shared.Status
import WeakAbsorption.Assets.Countermodels.Certified
import WeakAbsorption.Classification.Shared.Defs

namespace WeakAbsorption
namespace Classification
namespace Phase1
namespace Certified

open WeakAbsorption.Laws
open WeakAbsorption.Classification.Shared

/-
  ここは「証明済み」の層。
  実行探索の結果を theorem にしない。
  Registry にある定理を参照して、分類上の確定事実を置く。
-/

/-- M2 は C1 + C2' から一般には従わない（Registry の証明済み事実） -/
theorem m2_not_entailed_from_C1_C2p :
    ∃ (op : BinOp 4), HoldsC1P op ∧ HoldsC2pP op ∧ ¬ HoldsM2P op := by
  exact WeakAbsorption.Countermodels.not_entails_M2_from_C1_C2p

/-- 分類結果としての「証明済み refuted」記録（探索結果ではなく Registry ベース） -/
def m2CertifiedResult : ClassificationResult :=
  { name := "M2"
    status := CandidateStatus.refuted
    evidence :=
      Evidence.certifiedCountermodel
        4
        `WeakAbsorption.Countermodels.opM2_n4
        `WeakAbsorption.Countermodels.not_entails_M2_from_C1_C2p
    note := some "certified via Countermodels.Certified (Fin 4 countermodel)" }

/-- 軽い整合性チェック（これは重くない） -/
example : m2CertifiedResult.status = CandidateStatus.refuted := rfl

/-- 将来の拡張用：証明済み結果の一覧 -/
def certifiedResults : List ClassificationResult :=
  [m2CertifiedResult]

--#eval certifiedResults

end Certified
end Phase1
end Classification
end WeakAbsorption
