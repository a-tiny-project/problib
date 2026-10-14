module
public import Problib.Measure.Configuration.Unordered
public import Problib.Measure.Real.Order
public import Problib.Measure.Measurability.Real

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real
public section
attribute [local instance] Classical.propDecidable
universe u v w
variable {α : Type u}

/-- Sort a finite list by a real-valued key. -/
@[expose] public noncomputable def sortByKey (key : α → Real.Carrier)
    (values : List α) : List α :=
  values.mergeSort (fun left right =>
    decide (Problib.Real.Construction.Dedekind.le (key left) (key right)))

/-- Sorting preserves the unordered configuration. -/
public theorem sortByKey_perm (key : α → Real.Carrier)
    (values : List α) : (sortByKey key values).Perm values := by
  exact List.mergeSort_perm values _

/-- Permuted presentations have the same sorted list when the key is injective. -/
public theorem sortByKey_eq_of_perm (key : α → Real.Carrier)
    (injective : Function.Injective key) {left right : List α}
    (permutation : left.Perm right) :
    sortByKey key left = sortByKey key right := by
  let precedes := fun first second : α =>
    decide (Problib.Real.Construction.Dedekind.le (key first) (key second))
  have transitive : ∀ first second third : α,
      precedes first second → precedes second third → precedes first third := by
    intro first second third firstSecond secondThird
    exact decide_eq_true
      (Problib.Real.Construction.Dedekind.le_trans
        (of_decide_eq_true firstSecond) (of_decide_eq_true secondThird))
  have total : ∀ first second : α,
      precedes first second || precedes second first := by
    intro first second
    rcases Problib.Real.Construction.Dedekind.le_total (key first) (key second) with
      firstSecond | secondFirst
    · simp [precedes, firstSecond]
    · simp [precedes, secondFirst]
  have sorted (values : List α) :
      (sortByKey key values).Pairwise (fun first second => precedes first second = true) := by
    exact List.pairwise_mergeSort transitive total values
  apply List.Perm.eq_of_pairwise
    (le := fun first second => precedes first second = true)
    (fun first second _ _ firstSecond secondFirst =>
      injective (Problib.Real.Construction.Dedekind.le_antisymm
        (of_decide_eq_true firstSecond) (of_decide_eq_true secondFirst)))
    (sorted left) (sorted right)
  exact (sortByKey_perm key left).trans
    (permutation.trans (sortByKey_perm key right).symm)

public theorem unorder_sortByKey (key : α → Real.Carrier)
    (values : List α) :
    unorder (sortByKey key values) = unorder values :=
  Quotient.sound (sortByKey_perm key values)

/-- Choose the unique sorted presentation of an unordered configuration. -/
@[expose] public noncomputable def canonical (key : α → Real.Carrier)
    (injective : Function.Injective key) : Unordered α → List α :=
  Quotient.lift (sortByKey key)
    (fun _ _ permutation => sortByKey_eq_of_perm key injective permutation)

public theorem canonical_unorder (key : α → Real.Carrier)
    (injective : Function.Injective key) (values : List α) :
    canonical key injective (unorder values) = sortByKey key values := rfl

public theorem unorder_canonical (key : α → Real.Carrier)
    (injective : Function.Injective key) (configuration : Unordered α) :
    unorder (canonical key injective configuration) = configuration := by
  refine Quotient.inductionOn configuration ?_
  intro values
  change unorder (canonical key injective (unorder values)) = unorder values
  rw [canonical_unorder]
  exact unorder_sortByKey key values

/-- Insert a value before the first entry whose key is at least its own. -/
@[expose] public noncomputable def insertByKey (key : α → Real.Carrier) (value : α) :
    List α → List α
  | [] => [value]
  | entry :: rest =>
      if Problib.Real.Construction.Dedekind.le (key value) (key entry) then
        value :: entry :: rest
      else entry :: insertByKey key value rest

/-- Sort by inserting each entry into the sorted tail. -/
@[expose] public noncomputable def insertionSortByKey (key : α → Real.Carrier)
    (values : List α) : List α :=
  values.foldr (insertByKey key) []

public theorem insertByKey_perm (key : α → Real.Carrier) (value : α)
    (values : List α) : (insertByKey key value values).Perm (value :: values) := by
  induction values with
  | nil => exact List.Perm.refl _
  | cons entry rest induction =>
      unfold insertByKey
      by_cases before : Problib.Real.Construction.Dedekind.le (key value) (key entry)
      · rw [ite_eq_left before]
      · rw [ite_eq_right before]
        exact (List.Perm.cons entry induction).trans (List.Perm.swap value entry rest)

public theorem insertionSortByKey_perm (key : α → Real.Carrier)
    (values : List α) : (insertionSortByKey key values).Perm values := by
  induction values with
  | nil => exact List.Perm.refl _
  | cons head tail induction =>
      exact (insertByKey_perm key head _).trans (List.Perm.cons head induction)

private theorem insertByKey_pairwise (key : α → Real.Carrier) (value : α)
    {values : List α}
    (sorted : values.Pairwise (fun first second =>
      Problib.Real.Construction.Dedekind.le (key first) (key second))) :
    (insertByKey key value values).Pairwise (fun first second =>
      Problib.Real.Construction.Dedekind.le (key first) (key second)) := by
  induction values with
  | nil => exact List.pairwise_singleton _ _
  | cons entry rest induction =>
      rw [List.pairwise_cons] at sorted
      unfold insertByKey
      by_cases before : Problib.Real.Construction.Dedekind.le (key value) (key entry)
      · rw [ite_eq_left before, List.pairwise_cons, List.pairwise_cons]
        refine ⟨?_, sorted.1, sorted.2⟩
        intro other member
        rcases List.mem_cons.mp member with same | later
        · rw [same]
          exact before
        · exact Problib.Real.Construction.Dedekind.le_trans before (sorted.1 other later)
      · rw [ite_eq_right before, List.pairwise_cons]
        refine ⟨?_, induction sorted.2⟩
        intro other member
        rcases List.mem_cons.mp ((insertByKey_perm key value rest).mem_iff.mp member) with
          same | later
        · rw [same]
          rcases Problib.Real.Construction.Dedekind.le_total (key value) (key entry) with
            valueEntry | entryValue
          · exact False.elim (before valueEntry)
          · exact entryValue
        · exact sorted.1 other later

public theorem insertionSortByKey_pairwise (key : α → Real.Carrier)
    (values : List α) :
    (insertionSortByKey key values).Pairwise (fun first second =>
      Problib.Real.Construction.Dedekind.le (key first) (key second)) := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail induction => exact insertByKey_pairwise key head induction

/-- With an injective key, merge sorting and insertion sorting agree. -/
public theorem sortByKey_eq_insertionSortByKey (key : α → Real.Carrier)
    (injective : Function.Injective key) (values : List α) :
    sortByKey key values = insertionSortByKey key values := by
  have transitive : ∀ first second third : α,
      decide (Problib.Real.Construction.Dedekind.le (key first) (key second)) →
      decide (Problib.Real.Construction.Dedekind.le (key second) (key third)) →
      decide (Problib.Real.Construction.Dedekind.le (key first) (key third)) := by
    intro first second third firstSecond secondThird
    exact decide_eq_true
      (Problib.Real.Construction.Dedekind.le_trans
        (of_decide_eq_true firstSecond) (of_decide_eq_true secondThird))
  have total : ∀ first second : α,
      (decide (Problib.Real.Construction.Dedekind.le (key first) (key second)) ||
        decide (Problib.Real.Construction.Dedekind.le (key second) (key first))) := by
    intro first second
    rcases Problib.Real.Construction.Dedekind.le_total (key first) (key second) with
      firstSecond | secondFirst
    · simp [firstSecond]
    · simp [secondFirst]
  have merged : (sortByKey key values).Pairwise (fun first second =>
      Problib.Real.Construction.Dedekind.le (key first) (key second)) :=
    (List.pairwise_mergeSort transitive total values).imp
      (fun ordered => of_decide_eq_true ordered)
  exact List.Perm.eq_of_pairwise
    (le := fun first second =>
      Problib.Real.Construction.Dedekind.le (key first) (key second))
    (fun first second _ _ firstSecond secondFirst =>
      injective (Problib.Real.Construction.Dedekind.le_antisymm firstSecond secondFirst))
    merged (insertionSortByKey_pairwise key values)
    ((sortByKey_perm key values).trans (insertionSortByKey_perm key values).symm)

/-- One fold step of insertion that also carries the untouched suffix. -/
private noncomputable def insertStep (key : α → Real.Carrier)
    (input : α × ((List α × List α) × α)) : List α × List α :=
  (if Problib.Real.Construction.Dedekind.le (key input.2.2) (key input.1) then
      input.2.2 :: input.1 :: input.2.1.2
    else input.1 :: input.2.1.1,
    input.1 :: input.2.1.2)

private theorem insertStep_fold (key : α → Real.Carrier) (value : α)
    (values : List α) :
    values.foldr (fun head rest => insertStep key (head, rest, value)) ([value], []) =
      (insertByKey key value values, values) := by
  induction values with
  | nil => rfl
  | cons entry rest induction =>
      change insertStep key (entry, rest.foldr
        (fun head rest => insertStep key (head, rest, value)) ([value], []), value) = _
      rw [induction]
      rfl

private theorem insertStep_measurable {element : Space α} {key : α → Real.Carrier}
    (keyMeasurable : MeasurableMap element Real.borel key) :
    MeasurableMap
      (Space.product element
        (Space.product (Space.product (Space.list element) (Space.list element)) element))
      (Space.product (Space.list element) (Space.list element)) (insertStep key) := by
  unfold insertStep
  measurability [ListSpace.cons_measurable element]

/-- Inserting by a measurable key is jointly measurable in the list and the
inserted value. -/
public theorem insertByKey_measurable {element : Space α} {key : α → Real.Carrier}
    (keyMeasurable : MeasurableMap element Real.borel key) :
    MeasurableMap (Space.product (Space.list element) element) (Space.list element)
      (fun input => insertByKey key input.2 input.1) := by
  have folded : MeasurableMap (Space.product (Space.list element) element)
      (Space.product (Space.list element) (Space.list element))
      (fun input => input.1.foldr (fun head rest => insertStep key (head, rest, input.2))
        ([input.2], [])) := ListSpace.fold_measurable (parameter := element)
    (initial := fun value => ([value], ([] : List α)))
    (step := insertStep key)
    (by measurability [ListSpace.cons_measurable element])
    (insertStep_measurable keyMeasurable)
  have equal : (fun input : List α × α => insertByKey key input.2 input.1) =
      (fun input => (input.1.foldr (fun head rest => insertStep key (head, rest, input.2))
        ([input.2], [])).1) := by
    funext input
    rw [insertStep_fold]
  rw [equal]
  measurability

/-- Insertion sorting by a measurable key is measurable. -/
public theorem insertionSortByKey_measurable {element : Space α}
    {key : α → Real.Carrier}
    (keyMeasurable : MeasurableMap element Real.borel key) :
    MeasurableMap (Space.list element) (Space.list element)
      (insertionSortByKey key) := by
  have folded : MeasurableMap (Space.product (Space.list element) (Space.discrete Unit))
      (Space.list element)
      (fun input => input.1.foldr (fun head rest => insertByKey key head rest) []) :=
    ListSpace.fold_measurable (parameter := Space.discrete Unit)
    (initial := fun _ => ([] : List α))
    (step := fun input => insertByKey key input.1 input.2.1)
    (MeasurableMap.constant _ _ ([] : List α))
    (MeasurableMap.comp (insertByKey_measurable keyMeasurable)
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
        (Space.first_measurable _ _)))
  have attached : MeasurableMap (Space.list element)
      (Space.product (Space.list element) (Space.discrete Unit))
      (fun values => (values, ())) := by
    measurability
  exact fun {set} => MeasurableMap.comp folded attached (set := set)

/-- With an injective measurable key, sorting is measurable. -/
public theorem sortByKey_measurable {element : Space α} (key : α → Real.Carrier)
    (injective : Function.Injective key)
    (keyMeasurable : MeasurableMap element Real.borel key) :
    MeasurableMap (Space.list element) (Space.list element) (sortByKey key) := by
  have equal : sortByKey key = insertionSortByKey key :=
    funext (sortByKey_eq_insertionSortByKey key injective)
  rw [equal]
  measurability [insertionSortByKey_measurable keyMeasurable]

/-- Measurability of sorting is the sole remaining condition for the
canonical quotient section to be measurable. -/
public theorem canonical_measurable_of_sort {element : Space α}
    (key : α → Real.Carrier) (injective : Function.Injective key)
    (sortMeasurable : MeasurableMap (Space.list element) (Space.list element)
      (sortByKey key)) :
    MeasurableMap (Space.unordered element) (Space.list element)
      (canonical key injective) := by
  apply (unorder_quotient_map element).lift_measurable
  change MeasurableMap (Space.list element) (Space.list element) (sortByKey key)
  exact sortMeasurable

/-- The canonical sorted presentation of an unordered configuration is
measurable for an injective measurable key. -/
public theorem canonical_measurable {element : Space α}
    (key : α → Real.Carrier) (injective : Function.Injective key)
    (keyMeasurable : MeasurableMap element Real.borel key) :
    MeasurableMap (Space.unordered element) (Space.list element)
      (canonical key injective) :=
  canonical_measurable_of_sort key injective
    (sortByKey_measurable key injective keyMeasurable)

end
end Problib.Measure
