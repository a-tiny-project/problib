module

public import Problib.QuasiBorel.SFinite.Iteration
public meta import Trust.Claim

/-! Focused witnesses for represented positive recursion, including nonlinear
bodies and function-valued laws in a function-valued environment. -/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite.IterationWitnesses

public section

open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u v

@[trust_claim] theorem self_call_empty (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) :
    least (PositiveMap.identity X Y) = zeroFamily X Y := by
  apply below_antisymm
  · exact least_least _ _ (below_refl _)
  · exact zeroFamily_below _

@[trust_claim] theorem independent_child (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) (f : FamilyHom X Y) :
    least (PositiveMap.constant X Y f) = f :=
  (least_unfold (PositiveMap.constant X Y f)).symm

abbrev terminalSpace := Space.terminal realSource

@[expose] noncomputable def unitExit : FamilyHom terminalSpace terminalSpace :=
  unit terminalSpace

/-- The body exits or executes two recursive calls. Its pair of calls is a
nonlinear dependency on the continuation law. -/
@[expose] noncomputable def doubleCall :
    PositiveMap terminalSpace terminalSpace terminalSpace terminalSpace :=
  (PositiveMap.constant terminalSpace terminalSpace unitExit).add
    ((PositiveMap.identity terminalSpace terminalSpace).compose
      (PositiveMap.identity terminalSpace terminalSpace))

@[trust_claim] theorem doubleCall_operator (f : FamilyHom terminalSpace terminalSpace)
    (x : terminalSpace.Carrier) :
    doubleCall.operator f x = addFamily unitExit (Hom.comp (extend f) f) x := by
  rw [doubleCall, PositiveMap.add_operator]
  rfl

@[trust_claim] theorem doubleCall_first : unroll doubleCall 1 = unitExit := by
  apply Hom.ext
  intro x
  apply Law.ext
  change (doubleCall.operator (zeroFamily terminalSpace terminalSpace) x).val = (unitExit x).val
  rw [doubleCall_operator, addFamily_val]
  change Measure.add (unitExit x).val
    (bind (zero terminalSpace) (zeroFamily terminalSpace terminalSpace)).val = _
  rw [zero_bind]
  exact Measure.add_zero _

@[trust_claim] theorem doubleCall_second :
    unroll doubleCall 2 = addFamily unitExit unitExit := by
  change doubleCall.operator (unroll doubleCall 1) = _
  rw [doubleCall_first]
  apply Hom.ext
  intro x
  apply Law.ext
  rw [doubleCall_operator, addFamily_val, addFamily_val]
  change Measure.add (unitExit x).val (bind (pure terminalSpace x) (unit terminalSpace)).val = _
  rw [bind_unit]
  rfl

@[trust_claim] theorem doubleCall_second_mass :
    (unroll doubleCall 2 ()).val Set.univ = ENNReal.add ENNReal.one ENNReal.one := by
  rw [doubleCall_second, addFamily_val,
    Measure.add_apply_measurable _ _ (by exact terminalSpace.toMeasurable.univ)]
  change ENNReal.add ((pure terminalSpace ()).val Set.univ) ((pure terminalSpace ()).val Set.univ) = _
  rw [pure_val, Measure.dirac_apply_univ]

/-- The context is a function and the independent result is that function. -/
@[trust_claim] theorem function_environment_and_result
    (X : Space.{0, u} realSource) (Y : Space.{0, v} realSource) :
    let functions := Space.exponential X Y
    least (PositiveMap.constant functions functions (unit functions)) = unit functions :=
  independent_child _ _ _

/-- Two recursive children in a contextual bind use the captured environment. -/
@[trust_claim] theorem contextual_double_call
    (X : Space.{0, u} realSource) (Y : Space.{0, v} realSource)
    (f : FamilyHom X Y) :
    ((PositiveMap.identity X Y).bindContext
      (PositiveMap.call (Space.first X Y))).operator f =
      SFinite.bindContext f (Hom.comp f (Space.first X Y)) :=
  PositiveMap.bindContext_operator _ _ f

/-- The independent selector may return either branch without changing its
positive reading or restricting either branch's carrier to first order. -/
@[trust_claim] theorem case_left (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) (f : FamilyHom X Y) (x : X.Carrier) :
    ((PositiveMap.identity X Y).copair (PositiveMap.identity X Y)).operator f
      (Sum.inl x) = f x := rfl


/-- Every depth adds a unit-mass exit. The represented limit has infinite
mass, so this positive s-finite fixed point cannot be promoted to probability. -/
@[expose] noncomputable def infiniteExits :
    PositiveMap terminalSpace terminalSpace terminalSpace terminalSpace :=
  (PositiveMap.constant terminalSpace terminalSpace unitExit).add (PositiveMap.identity terminalSpace terminalSpace)

@[trust_claim] theorem infiniteExits_fuel_mass (n : Nat) :
    (unroll infiniteExits n ()).val Set.univ =
      ENNReal.partialSum (fun _ => ENNReal.one) n := by
  induction n with
  | zero => exact Measure.zero_apply Set.univ
  | succ n ih =>
      change (infiniteExits.operator (unroll infiniteExits n) ()).val Set.univ = _
      rw [infiniteExits, PositiveMap.add_operator]
      change (addFamily unitExit (unroll infiniteExits n) ()).val Set.univ = _
      rw [addFamily_val,
        Measure.add_apply_measurable _ _ (by exact terminalSpace.toMeasurable.univ), ih]
      change ENNReal.add ((pure terminalSpace ()).val Set.univ) _ = _
      rw [pure_val, Measure.dirac_apply_univ, ENNReal.partialSum, ENNReal.add_comm]

@[trust_claim] theorem infiniteExits_mass :
    (least infiniteExits ()).val Set.univ = ENNReal.top := by
  rw [least_apply infiniteExits () (by exact terminalSpace.toMeasurable.univ)]
  have equal := funext infiniteExits_fuel_mass
  rw [equal]
  exact ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero

end

end Problib.QuasiBorel.SFinite.IterationWitnesses
