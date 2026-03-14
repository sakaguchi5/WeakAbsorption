/-
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Rows

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

section RowAtoms

inductive RowSlot where
  | sqAbsorb
  | sqStable
  | decor
  | c2c1
deriving DecidableEq, Repr

structure RowAtom where
  slot    : RowSlot
  channel : CtxChannel
  tag     : CtxNFTag
deriving DecidableEq, Repr

def rowAtomsOfProfile (slot : RowSlot) (p : PurifiedCtxProfile) : List RowAtom :=
  match p.channel? with
  | none => []
  | some ch => p.tags.map (fun tag => { slot := slot, channel := ch, tag := tag })

def rowAtomsOfRow (row : PurifiedCtxRow) : List RowAtom :=
  rowAtomsOfProfile .sqAbsorb row.sqAbsorb ++
  rowAtomsOfProfile .sqStable row.sqStable ++
  rowAtomsOfProfile .decor row.decor ++
  rowAtomsOfProfile .c2c1 row.c2c1

def rowAtomsOfTarget (tg : CoreKernelTarget) : List RowAtom :=
  rowAtomsOfRow (corePurifiedRowOfTarget tg)

end RowAtoms

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption

-/
