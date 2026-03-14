import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.PackageBridge

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Instances
namespace R4

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore
open Core
--open Hypergraph

section Shape

/-- Canonical shape names of the audited R4 right-branch geometry. -/
abbrev sh_sqAbsorb_right : List RowShapeCoord := [(.sqAbsorb, .right)]
abbrev sh_sqAbsorb_left  : List RowShapeCoord := [(.sqAbsorb, .left)]
abbrev sh_decor_right    : List RowShapeCoord := [(.decor, .right)]
abbrev sh_decor_left     : List RowShapeCoord := [(.decor, .left)]
abbrev sh_sqStable_left  : List RowShapeCoord := [(.sqStable, .left)]
abbrev sh_hole_root      : List RowShapeCoord := [(.sqAbsorb, .root), (.c2c1, .root)]
abbrev sh_decorHole_root : List RowShapeCoord := [(.sqAbsorb, .root), (.decor, .root)]
abbrev sh_bridge_split   : List RowShapeCoord := [(.sqAbsorb, .left), (.decor, .right)]


/-- Package-side two-atomic but shape-collapsed duplication. -/
def PackageSameSlotSameChannelDuplication (tg : CoreKernelTarget) : Prop :=
  PackageIsTwoAtom tg ∧ (packageRowShape tg).length = 1

/-- Package-side pure, two-atomic, root-mixed shape. -/
def PackageRootMixedPureShape (tg : CoreKernelTarget) : Prop :=
  (r4SystemPackage tg).regime = .pure ∧
  PackageIsTwoAtom tg ∧
  (packageRowShape tg).length = 2 ∧
  ∀ sc, sc ∈ packageRowShape tg → sc.2 = .root

/-- Package-side bridge-split mixed shape. -/
def PackageBridgeSplitMixedShape (tg : CoreKernelTarget) : Prop :=
  (r4SystemPackage tg).regime = .bridgeSplit ∧
  packageRowShape tg = sh_bridge_split

theorem packageSameSlotSameChannelDuplication_iff_old (tg : CoreKernelTarget) :
    PackageSameSlotSameChannelDuplication tg ↔ SameSlotSameChannelDuplication tg := by
  constructor
  · intro h
    rcases h with ⟨hTwo, hLen⟩
    refine ⟨(packageIsTwoAtom_iff_old tg).1 hTwo, ?_⟩
    rw [packageRowShape_length_eq_old tg] at hLen
    exact hLen
  · intro h
    rcases h with ⟨hTwo, hLen⟩
    refine ⟨(packageIsTwoAtom_iff_old tg).2 hTwo, ?_⟩
    rw [packageRowShape_length_eq_old tg]
    exact hLen

theorem packageRootMixedPureShape_iff_old (tg : CoreKernelTarget) :
    PackageRootMixedPureShape tg ↔ RootMixedPureShape tg := by
  constructor
  · intro h
    rcases h with ⟨hReg, hTwo, hShape, hRoot⟩
    refine ⟨?_, (packageIsTwoAtom_iff_old tg).1 hTwo, ?_, (packageAllRoot_iff_old tg).1 hRoot⟩
    · simpa [packageRegime_eq_old tg] using hReg
    · rw [packageRowShape_length_eq_old tg] at hShape
      exact hShape
  · intro h
    rcases h with ⟨hReg, hTwo, hShape, hRoot⟩
    refine ⟨?_, (packageIsTwoAtom_iff_old tg).2 hTwo, ?_, (packageAllRoot_iff_old tg).2 hRoot⟩
    · simpa [packageRegime_eq_old tg] using hReg
    · rw [packageRowShape_length_eq_old tg]
      exact hShape

theorem packageBridgeSplitMixedShape_iff_old (tg : CoreKernelTarget) :
    PackageBridgeSplitMixedShape tg ↔ BridgeSplitMixedShape tg := by
  constructor
  · intro h
    rcases h with ⟨hReg, hShape⟩
    refine ⟨?_, ?_⟩
    · exact (packageRegime_system_iff_package tg .bridgeSplit).1 hReg
    · exact (packageRowShape_eq_iff_old tg sh_bridge_split).1 hShape
  · intro h
    rcases h with ⟨hReg, hShape⟩
    refine ⟨?_, ?_⟩
    · exact (packageRegime_system_iff_package tg .bridgeSplit).2 hReg
    · exact (packageRowShape_eq_iff_old tg sh_bridge_split).2 hShape

theorem package_aa_right_sameSlotSameChannelDuplication     : PackageSameSlotSameChannelDuplication .nfXASqAPred    := by exact (packageSameSlotSameChannelDuplication_iff_old _).2 aa_right_sameSlotSameChannelDuplication
theorem package_aa_leftLift_sameSlotSameChannelDuplication  : PackageSameSlotSameChannelDuplication .nfUSqLiftAPred := by exact (packageSameSlotSameChannelDuplication_iff_old _).2 aa_leftLift_sameSlotSameChannelDuplication

theorem package_hole_root_rootMixedPureShape                : PackageRootMixedPureShape .nfUHolePred                := by exact (packageRootMixedPureShape_iff_old _).2 hole_root_rootMixedPureShape
theorem package_decorHole_root_rootMixedPureShape           : PackageRootMixedPureShape .nfUDecorHolePred           := by exact (packageRootMixedPureShape_iff_old _).2 decorHole_root_rootMixedPureShape

theorem package_bridge_split_mixed_shape                    : PackageBridgeSplitMixedShape .nfUDecorRightPred       := by exact (packageBridgeSplitMixedShape_iff_old _).2 bridge_split_mixed_shape


theorem packageRowShape_nfXASqRightPred       : packageRowShape .nfXASqRightPred       = sh_sqAbsorb_right  := by rw [packageRowShape_eq_old]; exact rowShape_nfXASqRightPred_one_atom
theorem packageRowShape_nfUSqLiftRightSPred   : packageRowShape .nfUSqLiftRightSPred   = sh_sqAbsorb_left   := by rw [packageRowShape_eq_old]; exact rowShape_nfUSqLiftRightSPred_one_atom
theorem packageRowShape_nfXADecorRightPred    : packageRowShape .nfXADecorRightPred    = sh_decor_right     := by rw [packageRowShape_eq_old]; exact rowShape_nfXADecorRightPred_one_atom
theorem packageRowShape_nfUDecorLiftRightSPred: packageRowShape .nfUDecorLiftRightSPred= sh_decor_left      := by rw [packageRowShape_eq_old]; exact rowShape_nfUDecorLiftRightSPred_one_atom
theorem packageRowShape_nfXADecorLeftPred     : packageRowShape .nfXADecorLeftPred     = sh_decor_right     := by rw [packageRowShape_eq_old]; exact rowShape_nfXADecorLeftPred_one_atom
theorem packageRowShape_nfUDecorLiftLeftSPred : packageRowShape .nfUDecorLiftLeftSPred = sh_decor_left      := by rw [packageRowShape_eq_old]; exact rowShape_nfUDecorLiftLeftSPred_one_atom
theorem packageRowShape_nfUStablePred         : packageRowShape .nfUStablePred         = sh_sqStable_left   := by rw [packageRowShape_eq_old]; exact rowShape_nfUStablePred_one_atom
theorem packageRowShape_nfUHolePred           : packageRowShape .nfUHolePred           = sh_hole_root       := by rw [packageRowShape_eq_old]; exact rowShape_hole_root
theorem packageRowShape_nfUDecorHolePred      : packageRowShape .nfUDecorHolePred      = sh_decorHole_root  := by rw [packageRowShape_eq_old]; exact rowShape_decorHole_root
theorem packageRowShape_nfXASqAPred           : packageRowShape .nfXASqAPred           = sh_sqAbsorb_right  := by rw [packageRowShape_eq_old]; exact rowShape_aa_right
theorem packageRowShape_nfUSqLiftAPred        : packageRowShape .nfUSqLiftAPred        = sh_sqAbsorb_left   := by rw [packageRowShape_eq_old]; exact rowShape_aa_leftLift
theorem packageRowShape_nfUDecorRightPred     : packageRowShape .nfUDecorRightPred     = sh_bridge_split    := by rw [packageRowShape_eq_old]; exact rowShape_bridge_split

/-- Package-side one-atom shape catalog: five singleton shapes. -/
theorem package_one_atom_shape_cases (tg : CoreKernelTarget)
    (h1 : PackageIsOneAtom tg) :
    packageRowShape tg = sh_sqAbsorb_right ∨
    packageRowShape tg = sh_sqAbsorb_left ∨
    packageRowShape tg = sh_decor_right ∨
    packageRowShape tg = sh_decor_left ∨
    packageRowShape tg = sh_sqStable_left := by
  rcases package_one_atom_targets_exact tg h1 with h | h | h | h | h | h | h
  · exact Or.inl (by simpa [h] using packageRowShape_nfXASqRightPred)
  · exact Or.inr (Or.inl (by simpa [h] using packageRowShape_nfUSqLiftRightSPred))
  · exact Or.inr (Or.inr (Or.inl (by simpa [h] using packageRowShape_nfXADecorRightPred)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h] using packageRowShape_nfUDecorLiftRightSPred))))
  · exact Or.inr (Or.inr (Or.inl (by simpa [h] using packageRowShape_nfXADecorLeftPred)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h] using packageRowShape_nfUDecorLiftLeftSPred))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [h] using packageRowShape_nfUStablePred))))


/-- Package-side full row-shape catalog: eight extensional shapes. -/
theorem package_right_branch_shape_catalog (tg : CoreKernelTarget) :
    packageRowShape tg = sh_sqAbsorb_right ∨
    packageRowShape tg = sh_sqAbsorb_left ∨
    packageRowShape tg = sh_decor_right ∨
    packageRowShape tg = sh_decor_left ∨
    packageRowShape tg = sh_sqStable_left ∨
    packageRowShape tg = sh_hole_root ∨
    packageRowShape tg = sh_decorHole_root ∨
    packageRowShape tg = sh_bridge_split := by
  rcases package_exact_row_edge_card_small tg with h1 | h2
  · rcases package_one_atom_shape_cases tg h1 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases package_two_atom_targets_exact tg h2 with h | h | h | h | h
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageRowShape_nfUHolePred
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageRowShape_nfUDecorHolePred
    · exact Or.inl <|
        by simpa [h] using packageRowShape_nfXASqAPred
    · exact Or.inr <| Or.inl <|
        by simpa [h] using packageRowShape_nfUSqLiftAPred
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        by simpa [h] using packageRowShape_nfUDecorRightPred

/-- Package-side distinct row-shapes: the 8 canonical audited shapes. -/
def packageDistinctRowShapes : List (List RowShapeCoord) :=
  [ sh_sqAbsorb_right
  , sh_sqAbsorb_left
  , sh_decor_right
  , sh_decor_left
  , sh_sqStable_left
  , sh_hole_root
  , sh_decorHole_root
  , sh_bridge_split
  ]

theorem package_right_branch_shape_count_eight :
    packageDistinctRowShapes.length = 8 := by
  simp [packageDistinctRowShapes]

theorem packageDistinctRowShapes_nodup :
    packageDistinctRowShapes.Nodup := by
  decide

end Shape

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
