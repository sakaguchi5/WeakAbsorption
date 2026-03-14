import WeakAbsorption.Proof.Generators.Vars1.Independence.Witness.DoubleSq

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness

/-- Concrete root/neighbor targets used in the R4 root-behavior registry and certificates. -/
def xATerm : Term V := x.op A
def mTerm : Term V := vTerm.op (s.op vTerm)

def xASqHolePredTerm : Term V := xATerm.op (A.op A)
def xASqAPredTerm : Term V := x.op (A.op A)
def xASqLeftSPredTerm : Term V := x.op (A.op s)
def xASqRightSPredTerm : Term V := x.op (s.op A)
def xAStablePredTerm : Term V := x.op (A.op x)

def xADecorHolePredTerm : Term V := xATerm.op (A.op (A.op A))
def xADecorAPredTerm : Term V := x.op (A.op (s.op A))
def xADecorLeftSPredTerm : Term V := x.op (((s.op (x.op s))).op s)
def xADecorRightSPredTerm : Term V := x.op (s.op (s.op (x.op s)))

def uHolePredTerm : Term V := uTerm.op A
def uSqLiftHolePredTerm : Term V := xASqHolePredTerm.op s
def uSqLiftAPredTerm : Term V := xASqAPredTerm.op s
def uSqLiftLeftSPredTerm : Term V := xASqLeftSPredTerm.op s
def uSqLiftRightSPredTerm : Term V := xASqRightSPredTerm.op s
def uSqRightPredTerm : Term V := xATerm.op A
def uStablePredTerm : Term V := xAStablePredTerm.op s
def uDecorHolePredTerm : Term V := uTerm.op (s.op A)
def uDecorLiftHolePredTerm : Term V := xADecorHolePredTerm.op s
def uDecorLiftAPredTerm : Term V := xADecorAPredTerm.op s
def uDecorLiftLeftSPredTerm : Term V := xADecorLeftSPredTerm.op s
def uDecorLiftRightSPredTerm : Term V := xADecorRightSPredTerm.op s
def uDecorRightPredTerm : Term V := xATerm.op (s.op vTerm)



end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
