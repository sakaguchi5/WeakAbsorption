import WeakAbsorption.Assets.Countermodels.M2_n4

namespace WeakAbsorption
namespace Countermodels

/-- 反例資産: M2 は C1+C2' からは一般に従わない（Fin 4 反例） -/
theorem not_entails_M2_from_C1_C2p :
    ∃ (op : Laws.BinOp 4), Laws.HoldsC1P op ∧ Laws.HoldsC2pP op ∧ ¬ Laws.HoldsM2P op := by
  refine ⟨opM2_n4, opM2_n4_C1, opM2_n4_C2p, opM2_n4_not_M2⟩

end Countermodels
end WeakAbsorption
