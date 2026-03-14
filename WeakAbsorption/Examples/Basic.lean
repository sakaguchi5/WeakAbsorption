import WeakAbsorption.Core.Algebra
import WeakAbsorption.Core.Canonical
import WeakAbsorption.Proof.RewriteRoot
import WeakAbsorption.Proof.Counterexample.DistinctNormals
/-!
LAYER: EXAMPLES (models, counterexamples, phenomena)
MAY import: Canonical / Rewrite / Algebra as needed
MUST NOT be imported by: core/proofs (Quotient/Semantics/Free/Universal/Completeness)
Policy: examples must never leak dependencies back into theorem files.
-/
open WeakAbsorption.Closure
open WeakAbsorption.WAA

namespace WeakAbsorption
namespace Examples
namespace NAModel

inductive NA where
  | a | b | c
deriving DecidableEq, Repr

open NA
open WeakAbsorption

def opNA : NA → NA → NA
  | c, a => c
  | _, _ => a

theorem not_associative :
  ∃ x y z : NA, opNA (opNA x y) z ≠ opNA x (opNA y z) := by
  refine ⟨c, a, b, ?_⟩
  decide

-- NA を C12Algebra のモデルにする（C1,C2' を「計算で」証明）
def NA_alg : C12Algebra NA :=
{ op := opNA
  C1 := by
    intro x y
    cases x <;> cases y <;> decide
  C2p := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
}
end NAModel


/-- 異なる Normal だが RedEq 同値な具体例（最小級） -/
theorem exists_distinct_normals_RedEq (a : α) :
  ∃ u v : Term α, Normal u ∧ Normal v ∧ RedEq u v ∧ u ≠ v := by
  exact WeakAbsorption.Counterexample.exists_distinct_normals_RedEq (α := α) a

/-- ついで：NormalForm 上でも「異なるが NFRel で同値」な対が作れる（NFQuot が本当に潰している証拠） -/
theorem exists_distinct_NFRel (a : α) :
  ∃ x y : NormalForm α, x ≠ y ∧ NFRel (α := α) x y := by
  rcases exists_distinct_normals_RedEq (α := α) a with ⟨u, v, Nu, Nv, huv, unev⟩
  refine ⟨⟨u, Nu⟩, ⟨v, Nv⟩, ?_, ?_⟩
  · intro h
    apply unev
    exact congrArg Subtype.val h
  · exact huv

end Examples
end WeakAbsorption
