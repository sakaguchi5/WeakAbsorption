import WeakAbsorption.Proof.Generators.Vars1.Complete.Step16

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete

/--
Canonical import point for the vars=1 refutation of the two-kernel completeness claim.
-/
theorem twoKernelClosure_impossible :
  ¬ Step15.NFRelImpliesCtxCoreTplVars1 := by
  exact Step16.not_NFRelImpliesCtxCoreTplVars1

end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
