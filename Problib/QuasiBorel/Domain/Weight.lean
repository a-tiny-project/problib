module

public import Problib.QuasiBorel.Domain.Space
public import Problib.QuasiBorel.SFinite.Mass

/-!
# The weight predomain

This module formalizes the predomain `W` of extended nonnegative weights. Its
quasi-Borel space is the measurable weight space `SFinite.weightSpace`, so its
random elements are exactly the Borel measurable curves. Its order is
`ENNReal.le`, with countable chain suprema `ENNReal.iSup` and bottom zero.
Measurable curves are closed under pointwise suprema, which is the predomain
law. The unrestricted space on the same order would admit every curve and is
not used.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Domain.Predomain

public section

open Problib.Domain
open Problib.Measure hiding Space
open Problib.Real (ENNReal)
open Problib.QuasiBorel.SFinite (realSource weightSpace)

/-- Extended nonnegative weights ordered by `ENNReal.le`, with suprema `ENNReal.iSup`. -/
@[expose, implicit_reducible] noncomputable def weightOrder : CPO ENNReal where
  le := ENNReal.le
  refl := ENNReal.le_refl
  trans := ENNReal.le_trans
  antisymm := ENNReal.le_antisymm
  sup := fun chain _ => ENNReal.iSup chain
  below_sup := fun chain _ index => ENNReal.le_iSup chain index
  sup_least := fun _ _ _ below => ENNReal.iSup_le below

/-- The weight predomain `W` on the measurable weight space. -/
@[expose, implicit_reducible] noncomputable def weight : Predomain realSource where
  space := weightSpace
  order := weightOrder
  random_sup := fun _ _ accepted =>
    (ENNRealMeasurable.iSup (fun index =>
      ENNRealMeasurable.of_measurableMap (accepted index))).measurableMap

theorem weight_le (left right : ENNReal) :
    weight.order.le left right = ENNReal.le left right := rfl

theorem weight_sup (chain : Nat → ENNReal) (increasing : weight.order.Chain chain) :
    weight.order.sup chain increasing = ENNReal.iSup chain := rfl

theorem weight_bottom (value : ENNReal) : weight.order.le ENNReal.zero value :=
  ENNReal.zero_le value

end

end Problib.QuasiBorel.Domain.Predomain
