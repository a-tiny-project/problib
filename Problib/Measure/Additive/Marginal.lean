module

public import Problib.Measure.Additive.SFinite
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v w

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- The second-coordinate marginal of a joint measure. -/
@[expose] public def secondMarginal
    (joint : Measure (Space.product source target)) :
    Measure target :=
  joint.map Prod.snd (Space.second_measurable source target)

/-- Evaluating the second marginal on a measurable set equals the joint measure of
the cylinder set on that slice. -/
@[simp] public theorem secondMarginal_apply
    (joint : Measure (Space.product source target))
    {set : Set beta} (setMeasurable : target.Measurable set) :
    secondMarginal joint set =
      joint (Set.preimage Prod.snd set) :=
  joint.map_apply Prod.snd
    (Space.second_measurable source target) setMeasurable

/-- Mapping the first coordinate along any measurable function leaves the second
marginal unchanged. -/
public theorem secondMarginal_map_first {gamma : Type w} {ambient : Space gamma}
    (joint : Measure (Space.product source target))
    (function : alpha → gamma) (measurable : MeasurableMap source ambient function) :
    secondMarginal (joint.map (fun value => (function value.1, value.2))
      (Space.product_map measurable (MeasurableMap.identity target))) = secondMarginal joint := by
  rw [secondMarginal, map_comp joint (fun value => (function value.1, value.2)) Prod.snd
    (Space.product_map measurable (MeasurableMap.identity target))
    (Space.second_measurable ambient target)]
  rfl

/-- S-finiteness passes from a joint measure to its second marginal. -/
public noncomputable def secondMarginalSFinite
    {joint : Measure (Space.product source target)}
    (jointSFinite : SFinite joint) :
    SFinite (secondMarginal joint) :=
  jointSFinite.map Prod.snd
    (Space.second_measurable source target)

/-- Derive sigma-finiteness of a product joint measure from sigma-finiteness of
its second marginal across independent universes without an extra joint
finiteness premise. -/
public noncomputable def SigmaFinite.of_secondMarginal
    {joint : Measure (Space.product source target)}
    (finite : SigmaFinite (secondMarginal joint)) : SigmaFinite joint where
  sets := fun index => Set.preimage Prod.snd (finite.sets index)
  measurable := fun index => Space.second_measurable source target (finite.measurable index)
  monotone := fun {_ _} included {_} member => finite.monotone included member
  finite := by
    intro index
    rw [← secondMarginal_apply joint (finite.measurable index)]
    exact finite.finite index
  cover := by
    apply Set.ext
    intro value
    constructor
    · intro _
      exact True.intro
    · intro _
      have covered : Set.iUnion finite.sets value.2 := by
        rw [finite.cover]
        exact True.intro
      exact covered

/-- Restricting a joint measure to the preimage of a parameter region commutes with taking the second marginal. -/
public theorem secondMarginal_restrict_second
    (joint : Measure (Space.product source target)) {region : Set beta}
    (measurable : target.Measurable region) :
    Measure.secondMarginal (joint.restrict (Set.preimage Prod.snd region)) =
      (Measure.secondMarginal joint).restrict region :=
  Measure.map_restrict joint Prod.snd (Space.second_measurable source target) measurable

end Problib.Measure.Measure
