import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.Package
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowHypergraph

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

section Hypergraph

/-- Package-indexed exact support: the right-branch atoms read from the canonical R4 package. -/
def packageEdgeSupport (tg : CoreKernelTarget) : List R4System.Atom :=
  (r4SystemPackage tg).atoms

/-- The package-side exact-row vertex universe. -/
def packageExactRowVerts : List R4System.Atom :=
  exactRowAtomUniverse

/-- The 10 extensional exact supports of the audited R4 right-branch geometry. -/
abbrev supp_sqAbsorb_right_singleton : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .right, tag := .nfXA } ]

abbrev supp_sqAbsorb_left_singleton : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .left, tag := .nfU } ]

abbrev supp_decor_right_singleton : List RowAtom :=
  [ { slot := .decor, channel := .right, tag := .nfXA } ]

abbrev supp_decor_left_singleton : List RowAtom :=
  [ { slot := .decor, channel := .left, tag := .nfU } ]

abbrev supp_sqStable_left_singleton : List RowAtom :=
  [ { slot := .sqStable, channel := .left, tag := .nfU } ]

abbrev supp_hole_root : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .root, tag := .nfU }
  , { slot := .c2c1,     channel := .root, tag := .nfU } ]

abbrev supp_decorHole_root : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .root, tag := .nfUHolePred }
  , { slot := .decor,    channel := .root, tag := .nfU } ]

abbrev supp_aa_right : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .right, tag := .nfXA }
  , { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred } ]

abbrev supp_aa_leftLift : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .left, tag := .nfU }
  , { slot := .sqAbsorb, channel := .left, tag := .nfUSqLiftRightPred } ]

abbrev supp_bridge_split : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .left,  tag := .nfM }
  , { slot := .decor,    channel := .right, tag := .nfU } ]

/-- The package-side exact-row presentation of the audited R4 core as a finite multihypergraph. -/
structure R4PackageExactRowMultiHypergraph where
  verts : List RowAtom
  edgeSupport : CoreKernelTarget → List RowAtom
  verts_nodup : verts.Nodup
  edge_subset : ∀ tg a, a ∈ edgeSupport tg → a ∈ verts
  verts_card : verts.length = 13
  edge_small : ∀ tg, (edgeSupport tg).length = 1 ∨ (edgeSupport tg).length = 2

/-- Package projection agrees extensionally with the original target-indexed edge support. -/
theorem packageEdgeSupport_eq_old (tg : CoreKernelTarget) :
    packageEdgeSupport tg = r4ExactRowMultiHypergraph.edgeSupport tg := by
  have hPkgObs : packageEdgeSupport tg = observedRowAtoms tg := by
    simpa [packageEdgeSupport] using r4System_atoms_matches_observed tg
  have hObsOld : observedRowAtoms tg = rowAtomsOfTarget tg :=
    (rowAtoms_matches_observed tg).symm
  exact hPkgObs.trans (by simpa [r4ExactRowEdgeSupport] using hObsOld)

/-- Canonical package-side exact-row multihypergraph. -/
def r4PackageExactRowMultiHypergraph : R4PackageExactRowMultiHypergraph := by
  refine
    { verts := packageExactRowVerts
      edgeSupport := packageEdgeSupport
      verts_nodup := ?_
      edge_subset := ?_
      verts_card := ?_
      edge_small := ?_ }
  · simpa [packageExactRowVerts] using nodup_exactRowAtomUniverse
  · intro tg a ha
    rw [packageEdgeSupport_eq_old tg] at ha
    simpa [packageExactRowVerts] using rowAtomsOfTarget_subset_universe tg a ha
  · simpa [packageExactRowVerts] using r4_exact_row_vertex_card
  · intro tg
    rw [packageEdgeSupport_eq_old tg]
    exact r4_exact_row_edge_card_small tg

/-- The package-side exact-row semantics has exactly 13 atomic vertices. -/
theorem package_exact_row_vertex_card :
    r4PackageExactRowMultiHypergraph.verts.length = 13 :=
  r4PackageExactRowMultiHypergraph.verts_card

/-- Every package induces a 1-edge or a 2-edge. -/
theorem package_exact_row_edge_card_small (tg : CoreKernelTarget) :
    (r4PackageExactRowMultiHypergraph.edgeSupport tg).length = 1 ∨
    (r4PackageExactRowMultiHypergraph.edgeSupport tg).length = 2 :=
  r4PackageExactRowMultiHypergraph.edge_small tg

/-- One-atom predicate for the package-indexed exact-row multihypergraph. -/
def PackageIsOneAtom (tg : CoreKernelTarget) : Prop :=
  (r4PackageExactRowMultiHypergraph.edgeSupport tg).length = 1

/-- Two-atom predicate for the package-indexed exact-row multihypergraph. -/
def PackageIsTwoAtom (tg : CoreKernelTarget) : Prop :=
  (r4PackageExactRowMultiHypergraph.edgeSupport tg).length = 2

theorem package_one_atom_targets_exact (tg : CoreKernelTarget)
    (h1 : PackageIsOneAtom tg) :
    tg = .nfXASqRightPred ∨
    tg = .nfUSqLiftRightSPred ∨
    tg = .nfXADecorRightPred ∨
    tg = .nfUDecorLiftRightSPred ∨
    tg = .nfXADecorLeftPred ∨
    tg = .nfUDecorLiftLeftSPred ∨
    tg = .nfUStablePred := by
  change (packageEdgeSupport tg).length = 1 at h1
  rw [packageEdgeSupport_eq_old tg] at h1
  exact one_atom_targets_exact tg h1

theorem package_two_atom_targets_exact (tg : CoreKernelTarget)
    (h2 : PackageIsTwoAtom tg) :
    tg = .nfUHolePred ∨
    tg = .nfUDecorHolePred ∨
    tg = .nfXASqAPred ∨
    tg = .nfUSqLiftAPred ∨
    tg = .nfUDecorRightPred := by
  change (packageEdgeSupport tg).length = 2 at h2
  rw [packageEdgeSupport_eq_old tg] at h2
  exact two_atom_targets_exact tg h2

theorem packageEdgeSupport_nfXASqRightPred_exact :
    packageEdgeSupport .nfXASqRightPred = supp_sqAbsorb_right_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUSqLiftRightSPred_exact :
    packageEdgeSupport .nfUSqLiftRightSPred = supp_sqAbsorb_left_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfXADecorRightPred_exact :
    packageEdgeSupport .nfXADecorRightPred = supp_decor_right_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUDecorLiftRightSPred_exact :
    packageEdgeSupport .nfUDecorLiftRightSPred = supp_decor_left_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfXADecorLeftPred_exact :
    packageEdgeSupport .nfXADecorLeftPred = supp_decor_right_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUDecorLiftLeftSPred_exact :
    packageEdgeSupport .nfUDecorLiftLeftSPred = supp_decor_left_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUStablePred_exact :
    packageEdgeSupport .nfUStablePred = supp_sqStable_left_singleton := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUHolePred_exact :
    packageEdgeSupport .nfUHolePred = supp_hole_root := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfUDecorHolePred_exact :
    packageEdgeSupport .nfUDecorHolePred = supp_decorHole_root := by
  rw [packageEdgeSupport_eq_old]
  decide

theorem packageEdgeSupport_nfXASqAPred_exact :
    packageEdgeSupport .nfXASqAPred = supp_aa_right := by
  rw [packageEdgeSupport_eq_old]
  simpa [r4ExactRowEdgeSupport, supp_aa_right] using rowAtomsOfTarget_nfXASqAPred

theorem packageEdgeSupport_nfUSqLiftAPred_exact :
    packageEdgeSupport .nfUSqLiftAPred = supp_aa_leftLift := by
  rw [packageEdgeSupport_eq_old]
  simpa [r4ExactRowEdgeSupport, supp_aa_leftLift] using rowAtomsOfTarget_nfUSqLiftAPred

theorem packageEdgeSupport_nfUDecorRightPred_exact :
    packageEdgeSupport .nfUDecorRightPred = supp_bridge_split := by
  rw [packageEdgeSupport_eq_old]
  simpa [r4ExactRowEdgeSupport, supp_bridge_split] using rowAtomsOfTarget_nfUDecorRightPred

/-- Package-side full exact-support catalog: 10 extensional supports. -/
theorem package_right_branch_exact_support_catalog (tg : CoreKernelTarget) :
    packageEdgeSupport tg = supp_sqAbsorb_right_singleton ∨
    packageEdgeSupport tg = supp_sqAbsorb_left_singleton ∨
    packageEdgeSupport tg = supp_decor_right_singleton ∨
    packageEdgeSupport tg = supp_decor_left_singleton ∨
    packageEdgeSupport tg = supp_sqStable_left_singleton ∨
    packageEdgeSupport tg = supp_hole_root ∨
    packageEdgeSupport tg = supp_decorHole_root ∨
    packageEdgeSupport tg = supp_aa_right ∨
    packageEdgeSupport tg = supp_aa_leftLift ∨
    packageEdgeSupport tg = supp_bridge_split := by
  rcases package_exact_row_edge_card_small tg with h1 | h2
  · rcases package_one_atom_targets_exact tg h1 with h | h | h | h | h | h | h
    · exact Or.inl (by simpa [h] using packageEdgeSupport_nfXASqRightPred_exact)
    · exact Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfUSqLiftRightSPred_exact))
    · exact Or.inr (Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfXADecorRightPred_exact)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfUDecorLiftRightSPred_exact))))
    · exact Or.inr (Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfXADecorLeftPred_exact)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfUDecorLiftLeftSPred_exact))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h] using packageEdgeSupport_nfUStablePred_exact)))))
  · rcases package_two_atom_targets_exact tg h2 with h | h | h | h | h
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageEdgeSupport_nfUHolePred_exact
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageEdgeSupport_nfUDecorHolePred_exact
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageEdgeSupport_nfXASqAPred_exact
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        by simpa [h] using packageEdgeSupport_nfUSqLiftAPred_exact
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        by simpa [h] using packageEdgeSupport_nfUDecorRightPred_exact

/-- Package-side exact-row projection is still non-faithful. -/
theorem package_exact_row_projection_not_faithful :
    ∃ tg₁ tg₂ : CoreKernelTarget,
      tg₁ ≠ tg₂ ∧
      packageEdgeSupport tg₁ = packageEdgeSupport tg₂ := by
  rcases exact_row_projection_not_faithful with ⟨tg₁, tg₂, hne, heq⟩
  refine ⟨tg₁, tg₂, hne, ?_⟩
  rw [packageEdgeSupport_eq_old tg₁, packageEdgeSupport_eq_old tg₂]
  exact heq

/-- Package-side distinct exact supports, read as the old extensional quotient. -/
def packageDistinctEdgeSupports : List (List RowAtom) :=
  r4DistinctEdgeSupports

theorem packageDistinctEdgeSupports_eq_old :
    packageDistinctEdgeSupports = r4DistinctEdgeSupports :=
  rfl

theorem package_right_branch_exact_support_count_ten :
    packageDistinctEdgeSupports.length = 10 := by
  rw [packageDistinctEdgeSupports_eq_old]
  exact r4_distinct_edge_supports_card

end Hypergraph

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
