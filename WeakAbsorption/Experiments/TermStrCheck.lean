import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Proof.Generators.Orbit.Families.MixedCtx.WitnessK11K13

namespace WeakAbsorption
namespace Experiments
namespace TermStrCheck

open WeakAbsorption.SmallCheck
open WeakAbsorption.WAA.OrbitSafeMixedCtx
open WeakAbsorption.WAA.OrbitSafeMixedCtxK11K13Witness

/-
We print `termStr` for the concrete witness:
  plug (mixCtx a) (Au a) = x ⋆ (Au ⋆ x)
so you can visually compare it to SmallCheck logs like `ctx=(x⋆(□⋆x))`.
-/

def a : V := (0 : V)

-- Terms in vars=1
def X  : Term V := WeakAbsorption.WAA.OrbitSafeMixedCtxK11K13Witness.X  (a := a)
def S  : Term V := WeakAbsorption.WAA.OrbitSafeMixedCtxK11K13Witness.S  (a := a)
def A  : Term V := WeakAbsorption.WAA.OrbitSafeMixedCtxK11K13Witness.A  (a := a)
def Au : Term V := WeakAbsorption.WAA.OrbitSafeMixedCtxK11K13Witness.Au (a := a)

-- The context and the plugged term
def C : Ctx V := WeakAbsorption.WAA.OrbitSafeMixedCtx.mixCtx (α := V) a
def plugged : Term V := Ctx.plug C Au
/-
#eval termStr X --"x"
#eval termStr S --"(x⋆x)"
#eval termStr A --"((x⋆x)⋆(x⋆x))"
#eval termStr Au--"(((x⋆x)⋆(x⋆x))⋆x)"

#eval ctxStr C       --"(x⋆(□⋆x))"
#eval termStr plugged--"(x⋆((((x⋆x)⋆(x⋆x))⋆x)⋆x))"
-/

end TermStrCheck
end Experiments
end WeakAbsorption
