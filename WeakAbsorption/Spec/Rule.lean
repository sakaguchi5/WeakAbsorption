namespace WeakAbsorption
namespace Spec

/-- 生成器（ルール）の識別子。まずは既存の5本をそのまま通貨化する。 -/
inductive RuleId where
  | SqAbsorb | SqStable | C2C1 | Decor | DoubleSq
  deriving DecidableEq, Repr

/-- 有効化するルール集合（順序は意味を持たない想定） -/
abbrev RuleSet := List RuleId

/-- デフォルト：現状の5本全部を有効にする。 -/
def defaultRules : RuleSet :=
  [RuleId.SqAbsorb, RuleId.SqStable, RuleId.C2C1, RuleId.Decor, RuleId.DoubleSq]

end Spec
end WeakAbsorption
