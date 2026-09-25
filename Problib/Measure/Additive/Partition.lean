module

public import Problib.Measure.Additive.Core

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Partitioning an arbitrary set by a measurable set preserves total measure
under Caratheodory additivity. -/
public theorem inter_add_difference (measure : Measure space)
    (left : Set alpha) {right : Set alpha}
    (rightMeasurable : space.Measurable right) :
    ENNReal.add (measure (Set.inter left right))
      (measure (Set.difference left right)) = measure left :=
  (measure.isCaratheodory rightMeasurable left).symm

/-- Measures satisfy modularity across pairs of measurable sets. -/
public theorem union_add_inter (measure : Measure space)
    {left right : Set alpha} (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right) :
    ENNReal.add (measure (Set.union left right)) (measure (Set.inter left right)) =
      ENNReal.add (measure left) (measure right) := by
  have disjoint : Set.Disjoint right (Set.difference left right) :=
    fun {_} member outside => outside.2 member
  have unionMass := measure.union_disjoint rightMeasurable
    (space.difference leftMeasurable rightMeasurable) disjoint
  rw [Set.union_difference_absorb, Set.union_comm right left] at unionMass
  rw [unionMass, ENNReal.add_comm (measure right) (measure (Set.difference left right)),
    ENNReal.add_assoc, ENNReal.add_comm (measure right) (measure (Set.inter left right)),
    ← ENNReal.add_assoc,
    ENNReal.add_comm (measure (Set.difference left right)) (measure (Set.inter left right)),
    measure.inter_add_difference left rightMeasurable]

/-- The measure of a measurable region and the measure of its complement sum
to the total mass of the space. -/
public theorem add_complement (measure : Measure space) {region : Set alpha}
    (measurable : space.Measurable region) :
    ENNReal.add (measure region) (measure (Set.complement region)) =
      measure Set.univ := by
  have partition := measure.inter_add_difference Set.univ measurable
  have difference : Set.difference Set.univ region = Set.complement region := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.2, fun member => ⟨True.intro, member⟩⟩
  rw [Set.inter_univ_left, difference] at partition
  exact partition

end Problib.Measure.Measure
