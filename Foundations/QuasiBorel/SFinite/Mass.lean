module

public import Foundations.QuasiBorel.SFinite.Unit
public import Foundations.QuasiBorel.Measurable.Basic

/-!
# S-finite quasi-Borel law mass evaluation

This module formalizes the extended-nonnegative total mass evaluation morphism
on s-finite quasi-Borel laws into the quasi-Borel space `weightSpace` induced by
`ennrealBorel`, satisfying zero mass on zero laws and unit mass on Dirac masses.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (borel)
open Foundations.Real (ENNReal)

universe u

/-- Quasi-Borel space of extended nonnegative real numbers with its Borel structure. -/
@[expose] def weightSpace : Space realSource := Space.ofMeasurable borel ennrealBorel

theorem weight_measurable {space : Space.{0, u} realSource} (weight : Hom space weightSpace) :
    ENNRealMeasurable space.toMeasurable weight := by
  apply ENNRealMeasurable.ofMeasurableMap
  apply Space.measurableMap_iff_random.mpr
  intro random accepted
  exact weight.mapRandom accepted

/-- Quasi-Borel morphism evaluating the total mass of an s-finite law. -/
@[expose] noncomputable def mass (space : Space.{0, u} realSource) : Hom (object space) weightSpace where
  toFun := fun law => law.val Set.univ
  mapRandom := by
    intro random accepted
    exact (ENNRealMeasurable.comp (evaluation_measurable space space.toMeasurable.univ)
      (Space.random_measurable accepted)).measurableMap

@[simp] theorem mass_apply {space : Space.{0, u} realSource} (law : Law space) :
    mass space law = law.val Set.univ := rfl

@[simp] theorem mass_zero (space : Space.{0, u} realSource) :
    mass space (zero space) = ENNReal.zero :=
  Measure.zero_apply Set.univ

@[simp] theorem mass_pure {space : Space.{0, u} realSource} (point : space.Carrier) :
    mass space (pure space point) = ENNReal.one :=
  Measure.dirac_apply_univ space.toMeasurable point

end

end Foundations.QuasiBorel.SFinite
