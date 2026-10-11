module
public import Problib.Measure.Configuration.Power
public import Problib.Measure.Configuration.Unordered
public import Problib.Measure.Configuration.Reference
public import Problib.Measure.Kernel.Piecewise.Countable
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Composition.Bind.Transport
public import Problib.Measure.Additive.Atom
public import Problib.Measure.Product.Countable
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Integral.Density.Basic
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
import Problib.Measure.Measurability

set_option autoImplicit false

/-!
# Uniformly random orderings

A code of positions reorders a list by successive insertion. The uniform law on
codes gives the uniformly random ordering of a list as a Markov kernel, which
adds its head at a uniform position of its shuffled tail.
-/

namespace Problib.Measure
open Problib.Real
public section
attribute [local instance] Classical.propDecidable
universe u
variable {α : Type u} {element : Space α}

/-- Insertion codes: entry `k` of a code for a list of length `k + 1` places
the head at a position at most `k`. A position past the end clamps to the end,
so every code reorders its list. -/
@[expose] public def applyCode : List Nat → List α → List α
  | [], values => values
  | _ :: _, [] => []
  | position :: code, value :: values =>
      (applyCode code values).insertIdx
        (min position (applyCode code values).length) value

@[simp] public theorem applyCode_length :
    ∀ (code : List Nat) (values : List α),
      (applyCode code values).length = values.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | position :: code, value :: values => by
      rw [applyCode, List.length_insertIdx_of_le_length (Nat.min_le_right _ _),
        applyCode_length code values]
      rfl

/-- Every code reorders its list. -/
public theorem applyCode_perm :
    ∀ (code : List Nat) (values : List α), (applyCode code values).Perm values
  | [], values => List.Perm.refl values
  | _ :: _, [] => List.Perm.refl []
  | position :: code, value :: values => by
      rw [applyCode]
      exact (List.perm_insertIdx value _ (Nat.min_le_right _ _)).trans
        ((applyCode_perm code values).cons value)

/-- Each fixed code reorders lists measurably. -/
public theorem applyCode_measurable (element : Space α) (code : List Nat) :
    MeasurableMap (Space.list element) (Space.list element) (applyCode code) := by
  induction code with
  | nil => exact MeasurableMap.identity (Space.list element)
  | cons position code tail =>
      have inner : MeasurableMap (Space.product element (Space.list element))
          (Space.list element)
          (fun pair => (applyCode code pair.2).insertIdx
            (min position (applyCode code pair.2).length) pair.1) :=
        by measurability [insertIdx_measurable element, ListSpace.length_measurable element]
      have viewed : applyCode (position :: code) = (fun values =>
          Sum.elim (fun _ : Unit => ([] : List α))
            (fun pair : α × List α => (applyCode code pair.2).insertIdx
              (min position (applyCode code pair.2).length) pair.1)
            (ListSpace.view values)) := by
        funext values
        cases values <;> rfl
      rw [viewed]
      measurability [ListSpace.view_measurable element]

/-- Reordering is jointly measurable in the list and its code. -/
public theorem applyCode_joint_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.list element) (Space.list (Space.discrete Nat)))
      (Space.list element) (fun input => applyCode input.2 input.1) :=
  MeasurableMap.comp
    (positions_uncurry_measurable (function := applyCode)
      (applyCode_measurable element))
    (Space.swap_measurable _ _)

public theorem cons_code_measurable :
    MeasurableMap (Space.product (Space.list (Space.discrete Nat)) (Space.discrete Nat))
      (Space.list (Space.discrete Nat)) (fun input => input.2 :: input.1) :=
  MeasurableMap.comp (ListSpace.cons_measurable (Space.discrete Nat))
    (Space.swap_measurable _ _)

namespace Measure

/-- The uniform law on codes of each length with its s-finiteness
certificate. -/
@[expose] public noncomputable def codeLawWithFinite :
    (count : Nat) → Σ law : Measure (Space.list (Space.discrete Nat)), SFinite law
  | 0 => ⟨Measure.dirac _ [], SFinite.ofFinite (IsFinite.dirac _ _)⟩
  | count + 1 =>
      let previous := codeLawWithFinite count
      ⟨(Measure.prod previous.1 (uniformBelow (count + 1))
          (uniformBelowSFinite (count + 1))).map
          (fun input => input.2 :: input.1) cons_code_measurable,
        (SFinite.prod previous.2 (uniformBelowSFinite (count + 1))).map
          (fun input => input.2 :: input.1) cons_code_measurable⟩

/-- The uniform law on the `count!` codes for lists of length `count`. -/
@[expose] public noncomputable def codeLaw (count : Nat) :
    Measure (Space.list (Space.discrete Nat)) :=
  (codeLawWithFinite count).1

@[simp] public theorem codeLaw_zero : codeLaw 0 = Measure.dirac _ [] := rfl

public theorem codeLaw_succ (count : Nat) :
    codeLaw (count + 1) =
      (Measure.prod (codeLaw count) (uniformBelow (count + 1))
        (uniformBelowSFinite (count + 1))).map
        (fun input => input.2 :: input.1) cons_code_measurable := rfl

public noncomputable def SFinite.codeLaw (count : Nat) :
    SFinite (Measure.codeLaw count) :=
  (codeLawWithFinite count).2

private theorem prod_probability {β : Type u} {γ : Type} {first : Space β}
    {second : Space γ} {left : Measure first} {right : Measure second}
    (rightFinite : SFinite right) (leftProbability : IsProbability left)
    (rightProbability : IsProbability right) :
    IsProbability (Measure.prod left right rightFinite) := by
  constructor
  have productUniv : (Set.univ : Set (β × γ)) = Set.product Set.univ Set.univ := by
    funext input
    exact propext ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩
  rw [productUniv, Measure.prod_apply_product _ _ _ first.univ second.univ,
    leftProbability.univ_eq_one, rightProbability.univ_eq_one, ENNReal.one_mul]

/-- Every code law is a probability law. -/
public theorem codeLaw_probability (count : Nat) : IsProbability (codeLaw count) := by
  induction count with
  | zero => exact IsProbability.dirac _ _
  | succ count induction =>
      rw [codeLaw_succ]
      exact (prod_probability _ induction
        (uniformBelow_probability (Nat.succ_pos count))).map _ _

end Measure

/-- Pushing size-indexed code laws forward along a jointly measurable map gives
a measurable family of measures. -/
public theorem size_indexed_measurable {σ : Type u} {source : Space σ}
    {β : Type} {codes : Space β} (size : σ → Nat)
    (sizeMeasurable : MeasurableMap source (Space.discrete Nat) size)
    (laws : Nat → Measure codes) (finite : ∀ count, Measure.SFinite (laws count))
    (function : β → σ → List α)
    (joint : MeasurableMap (Space.product source codes)
      (Space.list element) (fun input => function input.2 input.1))
    (slice : ∀ input, MeasurableMap codes (Space.list element)
      (fun code => function code input))
    {set : Set (List α)} (setMeasurable : (Space.list element).Measurable set) :
    ENNRealMeasurable source (fun input =>
      ((laws (size input)).map (fun code => function code input)
        (slice input)) set) := by
  have fiber : ∀ count, source.Measurable (fun input => size input = count) :=
    fun count => sizeMeasurable (set := fun value => value = count) trivial
  have measured := (Kernel.countablePiecewise size fiber
    (fun count => (Kernel.attach (Kernel.const source (laws count))
      (Kernel.IsSFinite.const _ (finite count))).map _ joint)).measurable
    setMeasurable
  have equal : (fun input => Kernel.countablePiecewise size fiber
      (fun count => (Kernel.attach (Kernel.const source (laws count))
        (Kernel.IsSFinite.const _ (finite count))).map _ joint) input set) =
      (fun input => ((laws (size input)).map (fun code => function code input)
        (slice input)) set) := by
    funext input
    rw [Kernel.countablePiecewise_apply, Kernel.map_apply, Kernel.attach_apply,
      Kernel.const_apply, Measure.map_apply _ _ _ setMeasurable,
      Measure.map_apply _ _ _ (joint setMeasurable),
      Measure.map_apply _ _ _ setMeasurable]
    rfl
  rw [← equal]
  exact measured

/-- The uniformly random ordering of a list. -/
@[expose] public noncomputable def shuffle (element : Space α) :
    Kernel (Space.list element) (Space.list element) where
  toFun := fun values => (Measure.codeLaw values.length).map
    (fun code => applyCode code values)
    (positions_map_measurable (Space.list element) (fun code => applyCode code values))
  measurable := fun setMeasurable =>
    size_indexed_measurable List.length (ListSpace.length_measurable element)
      Measure.codeLaw Measure.SFinite.codeLaw applyCode
      (applyCode_joint_measurable element)
      (fun values => positions_map_measurable (Space.list element)
        (fun code => applyCode code values)) setMeasurable

public theorem shuffle_apply (values : List α) :
    shuffle element values = (Measure.codeLaw values.length).map
      (fun code => applyCode code values)
      (positions_map_measurable (Space.list element)
        (fun code => applyCode code values)) := rfl

/-- The random ordering is a Markov kernel. -/
public theorem shuffle_markov (values : List α) :
    Measure.IsProbability (shuffle element values) :=
  (Measure.codeLaw_probability values.length).map
    (fun code => applyCode code values)
    (positions_map_measurable (Space.list element) (fun code => applyCode code values))

public theorem insert_pair_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.product element (Space.list element))
        (Space.discrete Nat))
      (Space.list element) (fun input => input.1.2.insertIdx input.2 input.1.1) :=
  by measurability [insertIdx_measurable element]

/-- Uniform insertion of the first coordinate into the second is measurable in
the pair. -/
public theorem insertAtUniform_measurable (element : Space α)
    {set : Set (List α)} (setMeasurable : (Space.list element).Measurable set) :
    ENNRealMeasurable (Space.product element (Space.list element)) (fun input =>
      ((Measure.uniformBelow (input.2.length + 1)).map
        (fun position => input.2.insertIdx position input.1)
        (MeasurableMap.from_discrete (Space.list element)
          (fun position => input.2.insertIdx position input.1))) set) :=
  size_indexed_measurable (σ := α × List α) (β := Nat)
    (source := Space.product element (Space.list element))
    (codes := Space.discrete Nat) (fun input => input.2.length)
    (MeasurableMap.comp (ListSpace.length_measurable element)
      (Space.second_measurable _ _))
    (fun count => Measure.uniformBelow (count + 1))
    (fun count => Measure.uniformBelowSFinite (count + 1))
    (fun position input => input.2.insertIdx position input.1)
    (insert_pair_measurable element)
    (fun input => MeasurableMap.from_discrete (Space.list element)
      (fun position => input.2.insertIdx position input.1)) setMeasurable

/-- Insert the first coordinate at a uniform position of the second. -/
@[expose] public noncomputable def insertAtUniform (element : Space α) :
    Kernel (Space.product element (Space.list element)) (Space.list element) where
  toFun := fun input => (Measure.uniformBelow (input.2.length + 1)).map
    (fun position => input.2.insertIdx position input.1)
    (MeasurableMap.from_discrete (Space.list element)
      (fun position => input.2.insertIdx position input.1))
  measurable := fun setMeasurable =>
    insertAtUniform_measurable element setMeasurable

/-- Insert a value at a uniform position of a list. -/
@[expose] public noncomputable def insertUniform (element : Space α) (value : α) :
    Kernel (Space.list element) (Space.list element) :=
  (insertAtUniform element).precomp (fun values => (value, values))
    (Space.pair_measurable (MeasurableMap.constant _ element value)
      (MeasurableMap.identity _))

public theorem insertUniform_apply (value : α) (values : List α) :
    insertUniform element value values =
      (Measure.uniformBelow (values.length + 1)).map
        (fun position => values.insertIdx position value)
        (MeasurableMap.from_discrete (Space.list element) _) := rfl

/-- Shuffling a list adds its head at a uniform position of its shuffled
tail. -/
public theorem shuffle_cons (value : α) (values : List α) :
    shuffle element (value :: values) =
      (shuffle element values).bind (insertUniform element value) := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.bind_apply _ _ setMeasurable, shuffle_apply, shuffle_apply,
    lintegral_map _ _ _ ((insertUniform element value).measurable setMeasurable),
    Measure.map_apply _ _ _ setMeasurable]
  change Measure.codeLaw (values.length + 1) _ = _
  rw [Measure.codeLaw_succ, Measure.map_apply _ _ _
      (positions_map_measurable (Space.list element) _ setMeasurable),
    Measure.prod_apply _ _ _ (cons_code_measurable
      (positions_map_measurable (Space.list element) _ setMeasurable))]
  apply lintegral_congr
  intro code
  rw [insertUniform_apply, Measure.map_apply _ _ _ setMeasurable]
  change Measure.uniformBelow (values.length + 1) (fun position =>
      set ((applyCode code values).insertIdx
        (min position (applyCode code values).length) value)) =
    Measure.uniformBelow ((applyCode code values).length + 1) (fun position =>
      set ((applyCode code values).insertIdx position value))
  rw [applyCode_length]
  apply Measure.uniformBelow_congr
  intro position below
  rw [Nat.min_eq_left (Nat.le_of_lt_succ below)]

/-- Every map out of pairs of positions is measurable. -/
public theorem position_pair_measurable {β : Type _} (target : Space β)
    (function : Nat × Nat → β) :
    MeasurableMap (Space.product (Space.discrete Nat) (Space.discrete Nat)) target
      function :=
  MeasurableMap.uncurry_of_countable_first (fun index => index)
    (fun _ _ equal => equal)
    (function := fun first second => function (first, second))
    (fun first => MeasurableMap.from_discrete target (fun second => function (first, second)))

private theorem position_pair_set_measurable (set : Set (Nat × Nat)) :
    (Space.product (Space.discrete Nat) (Space.discrete Nat)).Measurable set :=
  position_pair_measurable (Space.discrete (Nat × Nat)) (fun pair => pair)
    (set := set) trivial

/-- The pair of positions that inserts two values in the opposite order and
reaches the same list. -/
@[expose] public def swapPositions (pair : Nat × Nat) : Nat × Nat :=
  if pair.1 < pair.2 then (pair.2 - 1, pair.1) else (pair.2, pair.1 + 1)

public theorem swapPositions_swapPositions (pair : Nat × Nat) :
    swapPositions (swapPositions pair) = pair := by
  rcases pair with ⟨first, second⟩
  by_cases before : first < second
  · have inner : ¬ second - 1 < first := by omega
    rw [show swapPositions (first, second) = (second - 1, first) from ite_eq_left before,
      show swapPositions (second - 1, first) = (first, second - 1 + 1) from
        ite_eq_right inner]
    exact Prod.ext rfl (show second - 1 + 1 = second by omega)
  · have inner : second < first + 1 := by omega
    rw [show swapPositions (first, second) = (second, first + 1) from ite_eq_right before,
      show swapPositions (second, first + 1) = (first + 1 - 1, second) from
        ite_eq_left inner]
    exact Prod.ext (show first + 1 - 1 = first by omega) rfl

/-- Swapping keeps a position pair inside the grid of valid double
insertions. -/
public theorem swapPositions_below {count : Nat} (pair : Nat × Nat)
    (below : pair.1 < count + 1 ∧ pair.2 < count + 2) :
    (swapPositions pair).1 < count + 1 ∧ (swapPositions pair).2 < count + 2 := by
  rcases pair with ⟨first, second⟩
  rcases below with ⟨firstBelow, secondBelow⟩
  by_cases before : first < second
  · rw [show swapPositions (first, second) = (second - 1, first) from ite_eq_left before]
    exact ⟨show second - 1 < count + 1 by omega, show first < count + 2 by omega⟩
  · rw [show swapPositions (first, second) = (second, first + 1) from ite_eq_right before]
    exact ⟨show second < count + 1 by omega, show first + 1 < count + 2 by omega⟩

/-- Two insertions commute once their positions are swapped. -/
public theorem insert_insert_swapPositions (values : List α) (x y : α)
    (pair : Nat × Nat) (below : pair.1 < values.length + 1 ∧
      pair.2 < values.length + 2) :
    (values.insertIdx pair.1 x).insertIdx pair.2 y =
      (values.insertIdx (swapPositions pair).1 y).insertIdx
        (swapPositions pair).2 x := by
  rcases pair with ⟨first, second⟩
  rcases below with ⟨firstBelow, secondBelow⟩
  by_cases before : first < second
  · rw [show swapPositions (first, second) = (second - 1, first) from ite_eq_left before]
    change (values.insertIdx first x).insertIdx second y =
      (values.insertIdx (second - 1) y).insertIdx first x
    have commuted := List.insertIdx_comm x y (i := first) (j := second - 1)
      (l := values) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ second)] at commuted
    exact commuted
  · rw [show swapPositions (first, second) = (second, first + 1) from ite_eq_right before]
    change (values.insertIdx first x).insertIdx second y =
      (values.insertIdx second y).insertIdx (first + 1) x
    exact (List.insertIdx_comm y x (i := second) (j := first) (l := values)
      (by omega) (by omega)).symm

namespace Measure

/-- The two uniform position laws for inserting into a list of length
`count`, then into its one-longer result. -/
@[expose] public noncomputable def uniformPairs (count : Nat) :
    Measure (Space.product (Space.discrete Nat) (Space.discrete Nat)) :=
  Measure.prod (uniformBelow (count + 1)) (uniformBelow (count + 2))
    (uniformBelowSFinite (count + 2))

private theorem uniformPairs_singleton (count : Nat) (pair : Nat × Nat) :
    uniformPairs count (Set.singleton pair) =
      if pair.1 < count + 1 ∧ pair.2 < count + 2 then
        ENNReal.mul (uniformWeight (count + 1)) (uniformWeight (count + 2))
      else ENNReal.zero := by
  rcases pair with ⟨first, second⟩
  have rectangle : Set.singleton (first, second) =
      Set.product (Set.singleton first) (Set.singleton second) := by
    funext pair
    apply propext
    constructor
    · intro equal
      rw [show pair = (first, second) from equal]
      exact ⟨rfl, rfl⟩
    · intro member
      exact Prod.ext member.1 member.2
  rw [uniformPairs, rectangle, Measure.prod_apply_product _ _ _ trivial trivial,
    uniformBelow_singleton, uniformBelow_singleton]
  by_cases firstBelow : first < count + 1
  · by_cases secondBelow : second < count + 2
    · rw [ite_eq_left firstBelow, ite_eq_left secondBelow, ite_eq_left ⟨firstBelow, secondBelow⟩]
    · rw [ite_eq_left firstBelow, ite_eq_right secondBelow,
        ite_eq_right (show ¬ ((first, second).1 < count + 1 ∧
          (first, second).2 < count + 2) from fun both => secondBelow both.2),
        ENNReal.mul_zero]
  · rw [ite_eq_right firstBelow,
      ite_eq_right (show ¬ ((first, second).1 < count + 1 ∧
        (first, second).2 < count + 2) from fun both => firstBelow both.1),
      ENNReal.zero_mul]

/-- Swapping position pairs preserves the uniform pair law. -/
public theorem uniformPairs_swap (count : Nat) :
    (uniformPairs count).map swapPositions
      (position_pair_measurable _ swapPositions) = uniformPairs count := by
  apply Measure.ext_of_atoms Problib.Countable.pairBijection.inverse
    (fun left right equal => by
      rw [← Problib.Countable.pairBijection.forward_inverse left, equal,
        Problib.Countable.pairBijection.forward_inverse])
    (fun pair => position_pair_set_measurable _)
  intro pair
  have preimage : Set.preimage swapPositions (Set.singleton pair) =
      Set.singleton (swapPositions pair) := by
    funext candidate
    apply propext
    constructor
    · intro equal
      change swapPositions candidate = pair at equal
      change candidate = swapPositions pair
      rw [← equal, swapPositions_swapPositions]
    · intro equal
      change candidate = swapPositions pair at equal
      change swapPositions candidate = pair
      rw [equal, swapPositions_swapPositions]
  rw [Measure.map_apply _ _ _ (position_pair_set_measurable _), preimage,
    uniformPairs_singleton, uniformPairs_singleton]
  by_cases below : pair.1 < count + 1 ∧ pair.2 < count + 2
  · rw [ite_eq_left (swapPositions_below pair below), ite_eq_left below]
  · have swappedOutside : ¬ ((swapPositions pair).1 < count + 1 ∧
        (swapPositions pair).2 < count + 2) := by
      intro swappedBelow
      apply below
      have back := swapPositions_below (swapPositions pair) swappedBelow
      rw [swapPositions_swapPositions] at back
      exact back
    rw [ite_eq_right swappedOutside, ite_eq_right below]

/-- Position pairs outside the valid grid are null. -/
public theorem uniformPairs_outside (count : Nat) :
    uniformPairs count (Set.complement (fun pair : Nat × Nat =>
      pair.1 < count + 1 ∧ pair.2 < count + 2)) = ENNReal.zero := by
  rw [uniformPairs, Measure.prod_apply _ _ _ (position_pair_set_measurable _)]
  rw [uniformBelow_lintegral_congr (right := fun _ => ENNReal.zero), lintegral_zero]
  intro first firstBelow
  rw [← uniformBelow_outside (count + 2)]
  apply uniformBelow_congr
  intro second secondBelow
  exact ⟨fun outside => absurd ⟨firstBelow, secondBelow⟩ outside,
    fun outside => absurd secondBelow outside⟩

end Measure

/-- Two uniform insertions in a row draw a uniform pair of positions. -/
public theorem insertUniform_bind (x y : α) (values : List α) :
    (insertUniform element x values).bind (insertUniform element y) =
      (Measure.uniformPairs values.length).map
        (fun pair => (values.insertIdx pair.1 x).insertIdx pair.2 y)
        (position_pair_measurable (Space.list element) _) := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.bind_apply _ _ setMeasurable, insertUniform_apply,
    lintegral_map _ _ _ ((insertUniform element y).measurable setMeasurable),
    Measure.map_apply _ _ _ setMeasurable, Measure.uniformPairs,
    Measure.prod_apply _ _ _ (position_pair_set_measurable _)]
  apply Measure.uniformBelow_lintegral_congr
  intro first below
  rw [insertUniform_apply, Measure.map_apply _ _ _ setMeasurable,
    List.length_insertIdx_of_le_length (Nat.le_of_lt_succ below)]
  rfl

/-- Uniform insertions of two values commute. -/
public theorem insertUniform_comm (x y : α) (values : List α) :
    (insertUniform element x values).bind (insertUniform element y) =
      (insertUniform element y values).bind (insertUniform element x) := by
  rw [insertUniform_bind, insertUniform_bind]
  conv => rhs; rw [← Measure.uniformPairs_swap values.length]
  rw [Measure.map_comp]
  exact Measure.map_congr_on _ (Measure.uniformPairs_outside values.length) _ _
    (fun pair below => insert_insert_swapPositions values x y pair below)

/-- Reordering a list does not change its random ordering. -/
public theorem shuffle_perm {left right : List α} (permutation : left.Perm right) :
    shuffle element left = shuffle element right := by
  induction permutation with
  | nil => rfl
  | cons value _ induction => rw [shuffle_cons, shuffle_cons, induction]
  | swap x y values =>
      have commuted : (insertUniform element x).comp (insertUniform element y) =
          (insertUniform element y).comp (insertUniform element x) :=
        Kernel.ext (fun current => by
          rw [Kernel.comp_apply, Kernel.comp_apply]
          exact insertUniform_comm x y current)
      rw [shuffle_cons, shuffle_cons, shuffle_cons, shuffle_cons,
        Measure.bind_assoc, Measure.bind_assoc, commuted]
  | trans _ _ first second => rw [first, second]

/-- The empty list has only its own ordering. -/
public theorem shuffle_nil : shuffle element [] = Measure.dirac (Space.list element) [] :=
  Measure.map_dirac (fun code => applyCode code ([] : List α))
    (positions_map_measurable (Space.list element) _) []

private theorem probability_map_const {β : Type _} {γ : Type _} {source : Space β}
    {target : Space γ} (law : Measure source) (probability : Measure.IsProbability law)
    (value : γ) :
    law.map (fun _ => value) (MeasurableMap.constant source target value) =
      Measure.dirac target value := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable, Measure.dirac_apply _ _ setMeasurable]
  by_cases member : set value
  · rw [ite_eq_left member]
    have whole : Set.preimage (fun _ : β => value) set = Set.univ :=
      funext fun _ => propext ⟨fun _ => True.intro, fun _ => member⟩
    rw [whole, probability.univ_eq_one]
  · rw [ite_eq_right member]
    have none : Set.preimage (fun _ : β => value) set = Set.empty :=
      funext fun _ => propext ⟨fun inside => member inside, fun impossible => impossible.elim⟩
    rw [none]
    exact law.empty_apply

/-- A random ordering of a list is the list itself once labels are
forgotten. -/
public theorem shuffle_unorder (values : List α) :
    (shuffle element values).map unorder (unorder_quotient_map element).measurable =
      Measure.dirac (Space.unordered element) (unorder values) := by
  rw [shuffle_apply, Measure.map_comp]
  have constant : (fun code => unorder (applyCode code values)) =
      (fun _ : List Nat => unorder values) :=
    funext fun code => Quotient.sound (applyCode_perm code values)
  rw [Measure.map_congr_function _ _
    (MeasurableMap.constant _ (Space.unordered element) (unorder values)) constant]
  exact probability_map_const _ (Measure.codeLaw_probability values.length) _

/-- From unordered to labelled configurations: a uniformly random ordering of
any presentation. -/
@[expose] public noncomputable def symmetrize (element : Space α) :
    Kernel (Space.unordered element) (Space.list element) where
  toFun := Quotient.lift (fun values => shuffle element values)
    (fun _ _ permutation => shuffle_perm permutation)
  measurable := by
    intro set setMeasurable
    apply ENNRealMeasurable.of_measurableMap
    apply (unorder_quotient_map element).lift_measurable
    exact ((shuffle element).measurable setMeasurable).measurableMap

public theorem symmetrize_apply (values : List α) :
    symmetrize element (unorder values) = shuffle element values := rfl

/-- Symmetrizing and then forgetting labels returns the configuration. -/
public theorem symmetrize_unorder (configuration : Unordered α) :
    (symmetrize element configuration).map unorder
        (unorder_quotient_map element).measurable =
      Measure.dirac (Space.unordered element) configuration := by
  refine Quotient.inductionOn configuration ?_
  intro values
  exact shuffle_unorder values

/-- A labelled law is exchangeable when a uniformly random reordering leaves
it unchanged. -/
@[expose] public def Exchangeable (law : Measure (Space.list element)) : Prop :=
  law.bind (shuffle element) = law

/-- An iid power of length `count + 1` inserts an independent draw at a uniform
position of the iid power of length `count`. -/
public theorem listPower_insertUniform_apply (reference : Measure element)
    (finite : Measure.SFinite reference) (count : Nat) {set : Set (List α)}
    (setMeasurable : (Space.list element).Measurable set) :
    Measure.listPower reference finite (count + 1) set =
      lintegral reference (fun value =>
        lintegral (Measure.listPower reference finite count)
          (fun values => insertUniform element value values set)) := by
  have insertMeasurable := insertIdx_measurable element setMeasurable
  have swappedMeasurable := Space.swap_measurable _ _ insertMeasurable
  rw [← Measure.insertion_uniform_power reference finite count,
    Measure.map_apply _ _ _ setMeasurable,
    ← Measure.prod_swap finite (Measure.SFinite.prod
      (Measure.SFinite.listPower finite count)
      (Measure.uniformBelowSFinite (count + 1))),
    Measure.map_apply _ _ _ insertMeasurable,
    Measure.prod_apply _ _ _ swappedMeasurable]
  apply lintegral_congr
  intro value
  have sliceMeasurable : (Space.product (Space.list element) (Space.discrete Nat)).Measurable
      (Set.preimage (fun values => (value, values))
        (Set.preimage (fun pair => (pair.2, pair.1))
          (Set.preimage (fun input => input.1.1.insertIdx input.1.2 input.2) set))) :=
    Kernel.verticalSection_measurable swappedMeasurable value
  rw [Measure.prod_apply _ _ _ sliceMeasurable]
  apply lintegral_congr_ae
  exact Measure.NullSet.mono (Measure.listPower_length_null reference finite count)
    (fun {values} failure lengthEqual => failure (by
      dsimp only
      rw [insertUniform_apply, Measure.map_apply _ _ _ setMeasurable, lengthEqual]
      rfl))

/-- Every ordered iid power is exchangeable. -/
public theorem listPower_exchangeable (reference : Measure element)
    (finite : Measure.SFinite reference) (count : Nat) :
    Exchangeable (Measure.listPower reference finite count) := by
  induction count with
  | zero =>
      change (Measure.listPower reference finite 0).bind (shuffle element) = _
      rw [Measure.listPower_zero, Measure.dirac_bind, shuffle_nil]
  | succ count induction =>
      have exchanged : (Measure.listPower reference finite count).bind
          (shuffle element) = Measure.listPower reference finite count := induction
      change (Measure.listPower reference finite (count + 1)).bind (shuffle element) = _
      apply Measure.ext
      intro set setMeasurable
      rw [listPower_insertUniform_apply reference finite count setMeasurable,
        Measure.bind_apply _ _ setMeasurable, Measure.listPower_succ,
        lintegral_map _ _ _ ((shuffle element).measurable setMeasurable),
        lintegral_prod _ _ _ (ENNRealMeasurable.comp
          ((shuffle element).measurable setMeasurable)
          (ListSpace.cons_measurable element))]
      apply lintegral_congr
      intro value
      calc lintegral (Measure.listPower reference finite count)
            (fun values => shuffle element (value :: values) set)
          = lintegral (Measure.listPower reference finite count) (fun values =>
              lintegral (shuffle element values)
                (fun current => insertUniform element value current set)) := by
            apply lintegral_congr
            intro values
            rw [shuffle_cons, Measure.bind_apply _ _ setMeasurable]
        _ = lintegral ((Measure.listPower reference finite count).bind
              (shuffle element))
              (fun current => insertUniform element value current set) :=
            (Measure.lintegral_bind _ _
              ((insertUniform element value).measurable setMeasurable)).symm
        _ = _ := by rw [exchanged]

/-- The summed configuration reference is exchangeable for every count
coefficient. -/
public theorem configurationReference_exchangeable (reference : Measure element)
    (finite : Measure.SFinite reference) (coefficient : Nat → NNReal) :
    Exchangeable (configurationReference reference finite coefficient) := by
  change (configurationReference reference finite coefficient).bind
    (shuffle element) = _
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.bind_apply _ _ setMeasurable, configurationReference, lintegral_sum,
    Measure.sum_apply _ setMeasurable]
  apply ENNReal.tsum_congr
  intro count
  rw [lintegral_smul_measure, Measure.smul_apply_measurable _ _ setMeasurable,
    ← Measure.bind_apply _ _ setMeasurable,
    show (Measure.listPower reference finite count).bind (shuffle element) =
      Measure.listPower reference finite count from
      listPower_exchangeable reference finite count]

/-- An exchangeable labelled law is its unordered law, symmetrized. -/
public theorem exchangeable_disintegration {law : Measure (Space.list element)}
    (exchangeable : Exchangeable law) :
    law = (law.map unorder (unorder_quotient_map element).measurable).bind
      (symmetrize element) := by
  rw [Measure.bind_map]
  have precomposed : (symmetrize element).precomp unorder
      (unorder_quotient_map element).measurable = shuffle element :=
    Kernel.ext (fun _ => rfl)
  rw [precomposed]
  exact exchangeable.symm

/-- The average of a labelled density over the orderings of a configuration. -/
@[expose] public noncomputable def orbitAverage (element : Space α)
    (density : List α → ENNReal) (configuration : Unordered α) : ENNReal :=
  lintegral (symmetrize element configuration) density

/-- The density form of `configuration_map_sound`: unordering averages a
labelled density over each orbit. -/
public theorem unorder_withDensity {reference : Measure (Space.list element)}
    (exchangeable : Exchangeable reference) {density : List α → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.list element) density) :
    (reference.withDensity density).map unorder
        (unorder_quotient_map element).measurable =
      (reference.map unorder (unorder_quotient_map element).measurable).withDensity
        (orbitAverage element density) := by
  have averageMeasurable : ENNRealMeasurable (Space.unordered element)
      (orbitAverage element density) :=
    Kernel.lintegral_measurable (symmetrize element) densityMeasurable
  have exchanged : reference.bind (shuffle element) = reference := exchangeable
  apply Measure.ext
  intro set setMeasurable
  have regionMeasurable := (unorder_quotient_map element).measurable setMeasurable
  have indicatorMeasurable :=
    ENNRealMeasurable.indicator regionMeasurable densityMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable,
    Measure.withDensity_apply _ _ regionMeasurable,
    Measure.withDensity_apply _ _ setMeasurable,
    ← Measure.map_restrict _ _ _ setMeasurable,
    lintegral_map _ _ _ averageMeasurable,
    ← lintegral_indicator _ _ regionMeasurable,
    ← lintegral_indicator _ _ regionMeasurable]
  calc lintegral reference (ennrealIndicator (Set.preimage unorder set) density)
      = lintegral (reference.bind (shuffle element))
          (ennrealIndicator (Set.preimage unorder set) density) := by
        rw [exchanged]
    _ = lintegral reference (fun values => lintegral (shuffle element values)
          (ennrealIndicator (Set.preimage unorder set) density)) :=
        Measure.lintegral_bind _ _ indicatorMeasurable
    _ = _ := by
        apply lintegral_congr
        intro values
        have same : ∀ code, unorder (applyCode code values) = unorder values :=
          fun code => Quotient.sound (applyCode_perm code values)
        rw [shuffle_apply, lintegral_map _ _ _ indicatorMeasurable]
        unfold ennrealIndicator ennrealPiecewise
        by_cases member : set (unorder values)
        · rw [ite_eq_left (show Set.preimage unorder set values from member)]
          change _ = lintegral (shuffle element values) density
          rw [shuffle_apply, lintegral_map _ _ _ densityMeasurable]
          apply lintegral_congr
          intro code
          rw [ite_eq_left (show Set.preimage unorder set (applyCode code values) by
            change set (unorder (applyCode code values))
            rw [same code]
            exact member)]
        · rw [ite_eq_right (show ¬ Set.preimage unorder set values from member)]
          refine (lintegral_congr _ (fun code => ?_)).trans
            (lintegral_zero (Measure.codeLaw values.length))
          rw [ite_eq_right (show ¬ Set.preimage unorder set (applyCode code values) by
            change ¬ set (unorder (applyCode code values))
            rw [same code]
            exact member)]

end
end Problib.Measure
