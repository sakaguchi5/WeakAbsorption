import WeakAbsorption.Tooling.ModelSearch.CounterexampleSearch
import WeakAbsorption.Tooling.Probe

open WeakAbsorption
/-
#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  | some op =>
      (WeakAbsorption.WAProbe.findK? op,
       WeakAbsorption.WAProbe.findS? op,
       WeakAbsorption.WAProbe.findY? op)
  | none =>
      (none, none, none)-/

  --(some 0, false, true)
/-
#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  | some op =>
      ( WeakAbsorption.Tooling.WAProbe.findY? op,
        WeakAbsorption.Tooling.WAProbe.isLeftAbsorbing op 0,
        WeakAbsorption.Tooling.WAProbe.isRightAbsorbing op 0 )
  | none => (none, false, false)

  --([0, 1, 2, 3], [0, 0, 0, 2], false, [0], [0], [0, 2], [0, 2])
-/
/-
#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  | some op =>
      ( WeakAbsorption.Tooling.WAProbe.allY op,
        WeakAbsorption.Tooling.WAProbe.yImage op 0,
        WeakAbsorption.Tooling.WAProbe.isConstantYImage op 0,
        (WeakAbsorption.Tooling.WAProbe.fixedPointsOf op 0,
         WeakAbsorption.Tooling.WAProbe.fixedPointsOf op 1,
         WeakAbsorption.Tooling.WAProbe.fixedPointsOf op 2,
         WeakAbsorption.Tooling.WAProbe.fixedPointsOf op 3) )
  | none => ([], [], false, ([],[],[],[]))

  --[(0, [0], [0], true), (1, [0], [0], true), (2, [0, 2], [0, 2], true), (3, [2], [0, 2], false)]
-/
/-
#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  | some op => WeakAbsorption.Tooling.WAProbe.reportRF op
  | none => []
-/
/-
#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  | some op => WeakAbsorption.Tooling.WAProbe.yIsVacuous op
  | none => false

  --true
 -/
