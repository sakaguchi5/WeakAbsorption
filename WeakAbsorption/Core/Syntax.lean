namespace WeakAbsorption
/-! ############################################################
## 1. Syntax
############################################################ -/

inductive Term (α : Type) where
  | var : α → Term α
  | op  : Term α → Term α → Term α
deriving DecidableEq, Repr

namespace Term
variable {α : Type}

-- Optional coercion: allows writing `(a : Term α)` as `a`.
instance : Coe α (Term α) where
  coe a := Term.var a

end Term
notation:70 a " ⋆ " b => Term.op a b
end WeakAbsorption
