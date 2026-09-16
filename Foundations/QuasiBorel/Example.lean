import Foundations.QuasiBorel.CartesianClosed

namespace Foundations.QuasiBorel.Example

def source : Source Nat :=
  Source.unrestricted Nat

abbrev naturals : Space source :=
  Space.unrestricted source Nat

def addition : Hom (Space.product naturals naturals) naturals where
  toFun := fun values => values.1 + values.2
  mapRandom := fun _ => True.intro

abbrev curriedAddition : Hom naturals (Space.exponential naturals naturals) :=
  Space.curry addition

theorem curriedAddition_applies (left right : Nat) :
    curriedAddition left right = left + right := rfl

theorem addition_roundtrip :
    Space.uncurry curriedAddition = addition :=
  Space.uncurry_curry addition

end Foundations.QuasiBorel.Example
