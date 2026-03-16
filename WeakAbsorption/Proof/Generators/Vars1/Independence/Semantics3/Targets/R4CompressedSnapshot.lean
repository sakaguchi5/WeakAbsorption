import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4StateLabelCompression

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core

/--
Catalog-level compressed snapshot for current audited R4.

This is not yet a general Core object.
It is the explicit compression image witnessed by the current
R4 factorization theorems:
- label-side core: `state`
- geometry-side core: `rowProfile`
-/
structure R4CompressedSnapshot where
  state : ObservedState
  rowProfile : ObservedRowProfile
  deriving DecidableEq, Repr

/--
Compress a Semantics3 snapshot to the current audited R4 compressed image.
This is meaningful for snapshots in the current R4 image.
-/
def compress (s : ObservedKernelSnapshot) : R4CompressedSnapshot :=
  { state := s.state
    rowProfile := s.rowProfile }

/--
Target-indexed compressed snapshot for the current audited R4 catalog.
-/
def compressedSnapshot (tg : ObservedTarget) : R4CompressedSnapshot :=
  { state := observedState tg
    rowProfile := observedRowProfile tg }

/--
Reconstruct an R4 snapshot from the compressed image.

This uses the catalog-level classifiers already established:
- `labelsOfState`
- `regimeOfState`
- `shapeFamilyOfProfile`
-/
def reconstruct (c : R4CompressedSnapshot) : ObservedKernelSnapshot :=
  { labels := labelsOfState c.state
    regime := regimeOfState c.state
    geometry := { rowProfile := c.rowProfile }
    shapeFamily := shapeFamilyOfProfile c.rowProfile }

/--
Compression of an observed target snapshot is exactly the expected pair
`(state, rowProfile)`.
-/
theorem compress_observedSnapshot
    (tg : ObservedTarget) :
    compress (observedSnapshot tg) = compressedSnapshot tg := by
  rfl

/--
`compress ∘ reconstruct = id` on the compressed image.
This is the easy direction and holds definitionally.
-/
theorem compress_reconstruct
    (c : R4CompressedSnapshot) :
    compress (reconstruct c) = c := by
  cases c
  rfl

/--
On the current audited R4 catalog, reconstruction after compression
recovers the original observed snapshot.
-/
theorem reconstruct_compress_observedSnapshot
    (tg : ObservedTarget) :
    reconstruct (compress (observedSnapshot tg)) = observedSnapshot tg := by
  calc
    reconstruct (compress (observedSnapshot tg))
        =
          { labels := labelsOfState (observedState tg)
            regime := regimeOfState (observedState tg)
            geometry := { rowProfile := observedRowProfile tg }
            shapeFamily := shapeFamilyOfProfile (observedRowProfile tg) } := by
              rfl
    _ = observedSnapshot tg := by
          simpa using
            (observedSnapshot_eq_reconstructed_from_state_and_rowProfile tg).symm

/--
Equivalent target-indexed form of the same reconstruction fact.
-/
theorem reconstruct_compressedSnapshot
    (tg : ObservedTarget) :
    reconstruct (compressedSnapshot tg) = observedSnapshot tg := by
  simpa [compressedSnapshot] using
    reconstruct_compress_observedSnapshot tg

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
