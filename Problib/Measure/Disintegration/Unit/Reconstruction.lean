module

public import Problib.Measure.Disintegration.Unit.Bounds
public import Problib.Measure.Additive.Marginal.Uniqueness
public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Real.Continuity
public import Problib.Measure.Real.Uniqueness

set_option autoImplicit false

namespace Problib.Measure.Measure.UnitDisintegration

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real

universe u

variable {beta : Type u} {target : Space beta}

private noncomputable def slice (joint : Measure (Space.product unitBorel target))
    (region : Set beta) : Measure unitBorel :=
  (joint.restrict (Set.preimage Prod.snd region)).map Prod.fst
    (Space.first_measurable unitBorel target)

private theorem slice_apply (joint : Measure (Space.product unitBorel target))
    (region : Set beta) {set : Set UnitInterval} (measurable : unitBorel.Measurable set) :
    slice joint region set = joint (Set.product set region) := by
  rw [slice, Measure.map_apply _ _ (Space.first_measurable unitBorel target) measurable,
    joint.restrict_apply _ (Space.first_measurable unitBorel target measurable)]
  rfl

private theorem slice_univ (joint : Measure (Space.product unitBorel target))
    {region : Set beta} (measurable : target.Measurable region) :
    slice joint region Set.univ = secondMarginal joint region := by
  rw [slice, Measure.map_apply _ _ (Space.first_measurable unitBorel target) unitBorel.univ,
    Set.preimage_univ, restrict_apply_univ, secondMarginal_apply joint measurable]

private theorem slice_finite (joint : Measure (Space.product unitBorel target))
    {region : Set beta} (measurable : target.Measurable region)
    (finite : ENNReal.Finite (secondMarginal joint region)) : IsFinite (slice joint region) := by
  constructor
  rw [slice_univ joint measurable]
  exact finite

private theorem conditional_initial_le_total
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (point : UnitInterval) (region : Set beta) :
    ENNReal.le (lintegral ((secondMarginal joint).restrict region)
      (fun input => conditional joint finite input (unitInitial point))) (secondMarginal joint region) := by
  have bound : ENNReal.le (lintegral ((secondMarginal joint).restrict region)
      (fun input => conditional joint finite input (unitInitial point)))
      (lintegral ((secondMarginal joint).restrict region) (fun _ => ENNReal.one)) := by
    apply lintegral_mono
    intro input
    rw [← (conditional_isProbability joint finite input).univ_eq_one]
    exact (conditional joint finite input).mono (Set.subset_univ _)
  rw [lintegral_const, ENNReal.one_mul, restrict_apply_univ] at bound
  exact bound

/-- On parameter regions of finite marginal measure the integrated conditional
initial-interval mass equals the initial marginal mass by right-density and
continuity from above. -/
public theorem conditional_initial_of_finite
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (point : UnitInterval)
    {region : Set beta} (measurable : target.Measurable region)
    (regionFinite : ENNReal.Finite (secondMarginal joint region)) :
    lintegral ((secondMarginal joint).restrict region)
      (fun input => conditional joint finite input (unitInitial point)) =
        initialMarginal joint point region := by
  apply ENNReal.le_antisymm
  · rw [initialMarginal_apply joint point measurable,
      ← slice_apply joint region (unitInitial_measurable point)]
    refine le_measure_unitInitial_of_right_dense (slice_finite joint measurable regionFinite)
      unitRationalBasis ?_ point ?_ ?_
    · intro left right less
      rcases exists_unitRationalBasis_between less with ⟨index, above, below⟩
      exact ⟨index, above, below.1⟩
    · rw [slice_univ joint measurable]
      exact conditional_initial_le_total joint finite point region
    · intro index active
      rw [slice_apply joint region (unitInitial_measurable _),
        ← initialMarginal_apply joint _ measurable]
      exact conditional_initial_le joint finite point index active measurable
  · exact le_conditional_initial joint finite point measurable

private theorem reconstructed_rectangle_univ
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint))
    {region : Set beta} (measurable : target.Measurable region) :
    reverseSemiproduct (secondMarginal joint) (conditional joint finite)
      (conditional_isFinite joint finite).toSFinite (Set.product Set.univ region) =
        secondMarginal joint region := by
  rw [reverseSemiproduct_apply_product _ _ _ unitBorel.univ measurable]
  have normalized : (fun input => conditional joint finite input Set.univ) =
      (fun _ => ENNReal.one) := by
    funext input
    exact (conditional_isProbability joint finite input).univ_eq_one
  rw [normalized, lintegral_const, ENNReal.one_mul, restrict_apply_univ]

/-- The reverse semiproduct of the second marginal and the unit conditional
kernel reconstructs the joint measure on all measurable product sets. -/
public theorem conditional_reconstruct
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) :
    reverseSemiproduct (secondMarginal joint) (conditional joint finite)
      (conditional_isFinite joint finite).toSFinite = joint := by
  let reconstructed := reverseSemiproduct (secondMarginal joint) (conditional joint finite)
    (conditional_isFinite joint finite).toSFinite
  apply ext_of_secondMarginal finite
  intro first second firstMeasurable secondMeasurable secondFinite
  have reconstructedFinite : IsFinite (slice reconstructed second) := by
    constructor
    rw [slice_apply reconstructed second unitBorel.univ]
    change ENNReal.Finite (reverseSemiproduct (secondMarginal joint) (conditional joint finite)
      (conditional_isFinite joint finite).toSFinite (Set.product Set.univ second))
    rw [reconstructed_rectangle_univ joint finite secondMeasurable]
    exact secondFinite
  have equal : slice reconstructed second = slice joint second := by
    apply finite_measure_ext_unitInitial reconstructedFinite (slice_finite joint secondMeasurable secondFinite)
    intro point
    rw [slice_apply reconstructed second (unitInitial_measurable point),
      slice_apply joint second (unitInitial_measurable point)]
    change reverseSemiproduct (secondMarginal joint) (conditional joint finite)
      (conditional_isFinite joint finite).toSFinite (Set.product (unitInitial point) second) = _
    rw [reverseSemiproduct_apply_product _ _ _ (unitInitial_measurable point) secondMeasurable,
      conditional_initial_of_finite joint finite point secondMeasurable secondFinite,
      initialMarginal_apply joint point secondMeasurable]
  have applied := congrArg (fun measure => measure first) equal
  simpa only [slice_apply _ _ firstMeasurable] using applied

/-- The integrated conditional initial interval matches initial marginal mass
on arbitrary measurable parameter regions including regions of infinite
marginal measure. -/
public theorem conditional_initial
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (point : UnitInterval)
    {region : Set beta} (measurable : target.Measurable region) :
    lintegral ((secondMarginal joint).restrict region)
      (fun input => conditional joint finite input (unitInitial point)) =
        initialMarginal joint point region := by
  rw [initialMarginal_apply joint point measurable]
  have equal := congrArg (fun measure : Measure (Space.product unitBorel target) =>
    measure (Set.product (unitInitial point) region)) (conditional_reconstruct joint finite)
  rw [reverseSemiproduct_apply_product _ _ _ (unitInitial_measurable point) measurable] at equal
  exact equal

end Problib.Measure.Measure.UnitDisintegration
