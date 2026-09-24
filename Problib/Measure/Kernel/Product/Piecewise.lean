module

public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Kernel.Piecewise
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Kernel.Measurable.Section

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- Restricting a semiproduct measure to a base region preimage equals the semiproduct with the restricted base measure. -/
public theorem semiproduct_restrict (measure : Measure source)
    (kernel : Kernel source target) (finite : Kernel.IsSFinite kernel)
    {region : Set alpha} (regionMeasurable : source.Measurable region) :
    (semiproduct measure kernel finite).restrict (Set.preimage Prod.fst region) =
      semiproduct (measure.restrict region) kernel finite := by
  apply Measure.ext
  intro set measurable
  rw [Measure.restrict_apply _ _ measurable,
    semiproduct_apply _ _ _ ((Space.product source target).inter measurable
      (Space.first_measurable source target regionMeasurable)),
    semiproduct_apply _ _ _ measurable, ← lintegral_indicator measure region regionMeasurable]
  apply lintegral_congr
  intro input
  classical
  by_cases member : region input
  · have equal : Set.preimage (fun value => (input, value))
        (Set.inter set (Set.preimage Prod.fst region)) =
        Set.preimage (fun value => (input, value)) set := by
      apply Set.ext
      intro value
      exact ⟨fun included => included.1, fun included => ⟨included, member⟩⟩
    rw [equal]
    simp only [ennrealIndicator, ennrealPiecewise, if_pos member]
  · have equal : Set.preimage (fun value => (input, value))
        (Set.inter set (Set.preimage Prod.fst region)) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun included => member included.2, False.elim⟩
    rw [equal, (kernel input).empty_apply]
    simp only [ennrealIndicator, ennrealPiecewise, if_neg member]

/-- Restricting a reverse semiproduct measure to a parameter region preimage equals the reverse semiproduct with the restricted base measure. -/
public theorem reverseSemiproduct_restrict (measure : Measure target)
    (kernel : Kernel target source) (finite : Kernel.IsSFinite kernel)
    {region : Set beta} (regionMeasurable : target.Measurable region) :
    (reverseSemiproduct measure kernel finite).restrict (Set.preimage Prod.snd region) =
      reverseSemiproduct (measure.restrict region) kernel finite := by
  rw [reverseSemiproduct, ← Measure.map_restrict _ _ _
    (Space.second_measurable source target regionMeasurable)]
  change ((semiproduct measure kernel finite).restrict (Set.preimage Prod.fst region)).map
    (fun value => (value.2, value.1)) (Space.swap_measurable target source) = _
  rw [semiproduct_restrict measure kernel finite regionMeasurable]
  rfl

/-- A semiproduct with a piecewise kernel splits into the sum of semiproducts on the base region and its complement. -/
public theorem semiproduct_piecewise (measure : Measure source) {region : Set alpha}
    (measurable : source.Measurable region) (inside outside : Kernel source target)
    (insideFinite : Kernel.IsSFinite inside) (outsideFinite : Kernel.IsSFinite outside) :
    semiproduct measure (Kernel.piecewise region measurable inside outside)
      (insideFinite.piecewise outsideFinite region measurable) =
    Measure.add (semiproduct (measure.restrict region) inside insideFinite)
      (semiproduct (measure.restrict (Set.complement region)) outside outsideFinite) := by
  apply Measure.ext
  intro set setMeasurable
  rw [semiproduct_apply _ _ _ setMeasurable,
    Measure.add_apply_measurable _ _ setMeasurable,
    semiproduct_apply _ _ _ setMeasurable,
    semiproduct_apply _ _ _ setMeasurable]
  have equal : (fun input => Kernel.piecewise region measurable inside outside input
      (Set.preimage (fun value => (input, value)) set)) =
      ennrealPiecewise region
        (fun input => inside input (Set.preimage (fun value => (input, value)) set))
        (fun input => outside input (Set.preimage (fun value => (input, value)) set)) := by
    funext input
    classical
    by_cases member : region input
    · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member]
      simp only [ennrealPiecewise, if_pos member]
    · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member]
      simp only [ennrealPiecewise, if_neg member]
  rw [equal]
  exact lintegral_piecewise measure measurable
    (Kernel.section_apply_measurable inside insideFinite setMeasurable)
    (Kernel.section_apply_measurable outside outsideFinite setMeasurable)

/-- A reverse semiproduct with a piecewise kernel splits into the sum of reverse semiproducts on the parameter region and its complement. -/
public theorem reverseSemiproduct_piecewise (measure : Measure target) {region : Set beta}
    (measurable : target.Measurable region) (inside outside : Kernel target source)
    (insideFinite : Kernel.IsSFinite inside) (outsideFinite : Kernel.IsSFinite outside) :
    reverseSemiproduct measure (Kernel.piecewise region measurable inside outside)
      (insideFinite.piecewise outsideFinite region measurable) =
    Measure.add (reverseSemiproduct (measure.restrict region) inside insideFinite)
      (reverseSemiproduct (measure.restrict (Set.complement region)) outside outsideFinite) := by
  rw [reverseSemiproduct, semiproduct_piecewise, Measure.map_add]
  rfl

end Problib.Measure.Measure
