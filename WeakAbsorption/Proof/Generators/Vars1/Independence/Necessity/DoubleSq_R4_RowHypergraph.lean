import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowCoordinates

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section RowHypergraph

/--
The exact-row presentation of the audited R4 core as a finite target-indexed multihypergraph.
Vertices are atomic row coordinates; each target induces one edge support.
We keep targets as labels, so equal supports for different targets are allowed.
-/
structure R4ExactRowMultiHypergraph where
  verts : List RowAtom
  edgeSupport : CoreKernelTarget → List RowAtom
  verts_nodup : verts.Nodup
  edge_subset : ∀ tg a, a ∈ edgeSupport tg → a ∈ verts
  verts_card : verts.length = 13
  edge_small : ∀ tg, (edgeSupport tg).length = 1 ∨ (edgeSupport tg).length = 2

/-- Vertex set of the exact-row multihypergraph. -/
def r4ExactRowVerts : List RowAtom :=
  exactRowAtomUniverse

/-- Target-indexed edge support. -/
def r4ExactRowEdgeSupport (tg : CoreKernelTarget) : List RowAtom :=
  rowAtomsOfTarget tg

/-- Canonical exact-row multihypergraph induced by the audited R4 semantic packages. -/
def r4ExactRowMultiHypergraph : R4ExactRowMultiHypergraph := by
  refine
    { verts := r4ExactRowVerts
      edgeSupport := r4ExactRowEdgeSupport
      verts_nodup := ?_
      edge_subset := ?_
      verts_card := ?_
      edge_small := ?_ }
  · simpa [r4ExactRowVerts] using nodup_exactRowAtomUniverse
  · intro tg a ha
    simpa [r4ExactRowEdgeSupport, r4ExactRowVerts] using
      rowAtomsOfTarget_subset_universe tg a ha
  · decide
  · intro tg
    cases tg <;> decide

/-- The exact-row semantics has exactly 13 atomic vertices. -/
theorem r4_exact_row_vertex_card :
    r4ExactRowMultiHypergraph.verts.length = 13 :=
  r4ExactRowMultiHypergraph.verts_card

/-- Every audited target induces a 1-edge or a 2-edge. -/
theorem r4_exact_row_edge_card_small (tg : CoreKernelTarget) :
    (r4ExactRowMultiHypergraph.edgeSupport tg).length = 1
      ∨
    (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2 :=
  r4ExactRowMultiHypergraph.edge_small tg

/-- One-atom predicate for the target-indexed exact-row multihypergraph. -/
def IsOneAtom (tg : CoreKernelTarget) : Prop :=
  (r4ExactRowMultiHypergraph.edgeSupport tg).length = 1

/-- Two-atom predicate for the target-indexed exact-row multihypergraph. -/
def IsTwoAtom (tg : CoreKernelTarget) : Prop :=
  (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2

/-- Exactly the seven audited targets below are 1-atomic. -/
theorem one_atom_targets_exact (tg : CoreKernelTarget)
    (h1 : (r4ExactRowMultiHypergraph.edgeSupport tg).length = 1) :
    tg = .nfXASqRightPred ∨
    tg = .nfUSqLiftRightSPred ∨
    tg = .nfXADecorRightPred ∨
    tg = .nfUDecorLiftRightSPred ∨
    tg = .nfXADecorLeftPred ∨
    tg = .nfUDecorLiftLeftSPred ∨
    tg = .nfUStablePred := by
  cases tg
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUHolePred).length = 1) := by
      decide
    exact hnot h1
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorHolePred).length = 1) := by
      decide
    exact hnot h1
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXASqAPred).length = 1) := by
      decide
    exact hnot h1
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUSqLiftAPred).length = 1) := by
      decide
    exact hnot h1
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorRightPred).length = 1) := by
      decide
    exact hnot h1

/-- Exactly the five audited targets below are 2-atomic. -/
theorem two_atom_targets_exact (tg : CoreKernelTarget)
    (h2 : (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2) :
    tg = .nfUHolePred ∨
    tg = .nfUDecorHolePred ∨
    tg = .nfXASqAPred ∨
    tg = .nfUSqLiftAPred ∨
    tg = .nfUDecorRightPred := by
  cases tg
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXASqRightPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUSqLiftRightSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXADecorRightPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorLiftRightSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfXADecorLeftPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUDecorLiftLeftSPred).length = 2) := by
      decide
    exact hnot h2
  · exfalso
    have hnot :
        ¬ ((r4ExactRowMultiHypergraph.edgeSupport CoreKernelTarget.nfUStablePred).length = 2) := by
      decide
    exact hnot h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- Convenience wrapper from the `IsTwoAtom` predicate. -/
theorem two_atom_targets_exact_of_IsTwoAtom (tg : CoreKernelTarget)
    (h : IsTwoAtom tg) :
    tg = .nfUHolePred ∨
    tg = .nfUDecorHolePred ∨
    tg = .nfXASqAPred ∨
    tg = .nfUSqLiftAPred ∨
    tg = .nfUDecorRightPred := by
  change (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2 at h
  exact two_atom_targets_exact tg h

/-- The bridge-split target induces a 2-edge. -/
theorem bridge_split_has_two_atoms :
    (r4ExactRowMultiHypergraph.edgeSupport .nfUDecorRightPred).length = 2 := by
  decide

/-- There are pure targets whose exact row support is also a 2-edge. -/
theorem pure_two_atom_edge_exists :
    ∃ tg : CoreKernelTarget,
      packageRegime tg = .pure ∧
      (r4ExactRowMultiHypergraph.edgeSupport tg).length = 2 := by
  refine ⟨.nfXASqAPred, ?_, ?_⟩
  · decide
  · decide

/-- Therefore bridge-split is not characterized by row-support cardinality alone. -/
theorem bridge_split_not_characterized_by_cardinality :
    ∃ tg₁ tg₂ : CoreKernelTarget,
      packageRegime tg₁ = .bridgeSplit ∧
      packageRegime tg₂ = .pure ∧
      (r4ExactRowMultiHypergraph.edgeSupport tg₁).length =
        (r4ExactRowMultiHypergraph.edgeSupport tg₂).length := by
  refine ⟨.nfUDecorRightPred, .nfXASqAPred, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/--
The exact-row projection forgets part of the package data:
distinct targets can induce the same exact-row edge support.
-/
theorem exact_row_projection_not_faithful :
    ∃ tg₁ tg₂ : CoreKernelTarget,
      tg₁ ≠ tg₂ ∧
      r4ExactRowMultiHypergraph.edgeSupport tg₁ =
        r4ExactRowMultiHypergraph.edgeSupport tg₂ := by
  refine ⟨.nfXADecorRightPred, .nfXADecorLeftPred, ?_, ?_⟩
  · decide
  · decide

/-- Extensional edge supports, quotienting the target labels away. -/
def r4DistinctEdgeSupports : List (List RowAtom) :=
  (allCoreKernelTargets.map rowAtomsOfTarget).eraseDups

/-- The extensional quotient of the multihypergraph has no duplicate edges. -/
theorem nodup_r4DistinctEdgeSupports :
    r4DistinctEdgeSupports.Nodup := by
  decide

/-- The extensional quotient has exactly 10 distinct edge supports. -/
theorem r4_distinct_edge_supports_card :
    r4DistinctEdgeSupports.length = 10 := by
  decide

/-- Optional coarse quotient of exact support: forget tags, keep only slot × channel incidence. -/
def rowShapeOfTarget (tg : CoreKernelTarget) : List (RowSlot × CtxChannel) :=
  (rowAtomsOfTarget tg).map (fun a => (a.slot, a.channel)) |>.eraseDups

end RowHypergraph

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
