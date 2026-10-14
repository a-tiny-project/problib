module

public import Problib.Inference.SplitMerge.Matter
public import Problib.Inference.Weighting
public import Problib.Inference.Population
public import Problib.Measure.Configuration.Unordered

set_option autoImplicit false

/-!
# Label-free matter outputs

The matter state labels its clusters by list position and its patches by
position within a cluster. Forgetting both labels leaves an unordered
collection of clusters, each a parent with an unordered collection of patches,
beside the unordered background (`matterUnorder`). Any read-out that depends
only on this label-free state factors through its law, and weighted draws and
populations of matter states carry over to it by W1's `weighted_map` and
`empirical_map`.
-/

namespace Problib.Inference

open Problib.Measure

universe u

public section

variable {α β : Type u}

/-- Mapping every entry of a list by a measurable map is measurable. -/
theorem list_map_measurable {element : Space α} {result : Space β} {function : α → β}
    (measurable : MeasurableMap element result function) :
    MeasurableMap (Space.list element) (Space.list result) (List.map function) := by
  have folded : MeasurableMap (Space.product (Space.list element) (Space.discrete Unit))
      (Space.list result)
      (fun input => input.1.foldr (fun head rest => function head :: rest) []) :=
    ListSpace.fold_measurable (initial := fun _ => ([] : List β))
      (step := fun input => function input.1 :: input.2.1)
      (MeasurableMap.constant _ _ [])
      (MeasurableMap.comp (ListSpace.cons_measurable result)
        (Space.pair_measurable (MeasurableMap.comp measurable (Space.first_measurable _ _))
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))))
  have composed : MeasurableMap (Space.list element) (Space.list result)
      (fun values => values.foldr (fun head rest => function head :: rest) []) :=
    MeasurableMap.comp folded
      (Space.pair_measurable (MeasurableMap.identity _)
        (MeasurableMap.constant _ (Space.discrete Unit) ()))
  have equal : List.map function =
      (fun values => values.foldr (fun head rest => function head :: rest) []) := by
    funext values
    induction values with
    | nil => rfl
    | cons head tail induction => rw [List.map_cons, induction]; rfl
  rw [equal]
  exact fun {set} => composed (set := set)

variable {P Q : Type u} {parents : Space P} {patches : Space Q}

/-- Forget the cluster labels and the patch labels within each cluster and
in the background. -/
@[expose] def matterUnorder (state : List (P × List Q) × List Q) :
    Unordered (P × Unordered Q) × Unordered Q :=
  (unorder (state.1.map (fun cluster => (cluster.1, unorder cluster.2))), unorder state.2)

theorem matterUnorder_measurable :
    MeasurableMap (matterSpace parents patches)
      (Space.product (Space.unordered (Space.product parents (Space.unordered patches)))
        (Space.unordered patches))
      (matterUnorder (P := P) (Q := Q)) :=
  Space.pair_measurable
    (MeasurableMap.comp (unorder_quotient_map _).measurable
      (MeasurableMap.comp
        (list_map_measurable (Space.pair_measurable (Space.first_measurable _ _)
          (MeasurableMap.comp (unorder_quotient_map patches).measurable
            (Space.second_measurable _ _))))
        (Space.first_measurable _ _)))
    (MeasurableMap.comp (unorder_quotient_map patches).measurable (Space.second_measurable _ _))

/-- A read-out of the label-free state has the law of the label-free state,
read out. -/
example {γ : Type u} {result : Space γ} (law : Measure (matterSpace parents patches))
    {readOut : Unordered (P × Unordered Q) × Unordered Q → γ}
    (readOutMeasurable : MeasurableMap
      (Space.product (Space.unordered (Space.product parents (Space.unordered patches)))
        (Space.unordered patches)) result readOut) :
    law.map (fun state => readOut (matterUnorder state))
        (MeasurableMap.comp readOutMeasurable matterUnorder_measurable) =
      (law.map matterUnorder matterUnorder_measurable).map readOut readOutMeasurable := by
  rw [Measure.map_comp]

/-- Weighted matter draws carry their proper weighting to the label-free state.
-/
example {target : Measure (matterSpace parents patches)}
    {weighted : Measure (Space.product (matterSpace parents patches) weightSpace)}
    (properlyWeighted : ProperlyWeighted target weighted) :
    ProperlyWeighted (target.map matterUnorder matterUnorder_measurable)
      (weighted.map (fun draw => (matterUnorder draw.1, draw.2))
        (value_map_measurable matterUnorder_measurable)) :=
  weighted_map matterUnorder_measurable properlyWeighted

/-- Populations of matter states carry their empirical invariance to the
label-free state. -/
example {ι : Type} {lanes : Lanes ι} {target : Measure (matterSpace parents patches)}
    {population : Measure (populationSpace ι (matterSpace parents patches))}
    (invariant : EmpiricalInvariant lanes target population) :
    EmpiricalInvariant lanes (target.map matterUnorder matterUnorder_measurable)
      (population.map (lanewise matterUnorder) (lanewise_measurable matterUnorder_measurable)) :=
  empirical_map matterUnorder_measurable invariant

end
end Problib.Inference
