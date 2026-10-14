module
public import Problib.Measure.Configuration.Position
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Additive.SFinite
public import Problib.Measure.Kernel.Product.Transport
import Problib.Measure.Measurability

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real
public section
attribute [local instance] Classical.propDecidable
universe u
variable {α : Type u} {element : Space α}

namespace Measure

/-- Uniformly weighted counting on `{0, ..., bound-1}`. -/
@[expose] public noncomputable def uniformBelow (bound : Nat) :
    Measure (Space.discrete Nat) :=
  Measure.smul (ENNReal.finite (NNReal.div NNReal.one
      (NNReal.ofReal (Problib.Real.Construction.Dedekind.selection.ofRat
        (bound : Rat)))))
    (Measure.sum (fun index =>
      if index < bound then Measure.dirac (Space.discrete Nat) index
      else Measure.zero _))

public noncomputable def uniformBelowSFinite (bound : Nat) :
    SFinite (uniformBelow bound) := by
  let components : Nat → Measure (Space.discrete Nat) := fun index =>
    if index < bound then Measure.dirac (Space.discrete Nat) index
    else Measure.zero _
  have finite : ∀ index, SFinite (components index) := by
    intro index
    dsimp [components]
    split
    · exact SFinite.ofFinite (IsFinite.dirac _ _)
    · exact SFinite.zero _
  exact (SFinite.sum components finite).smul _ (by trivial)

/-- Construct each ordered iid power with its s-finiteness certificate. -/
@[expose] public noncomputable def listPowerWithFinite
    (reference : Measure element) (finite : SFinite reference) :
    (count : Nat) → Σ law : Measure (Space.list element), SFinite law
  | 0 =>
      ⟨Measure.dirac _ [], SFinite.ofFinite (IsFinite.dirac _ _)⟩
  | count + 1 =>
      let previous := listPowerWithFinite reference finite count
      let law := (Measure.prod reference previous.1 previous.2).map
        (fun input => input.1 :: input.2) (ListSpace.cons_measurable element)
      ⟨law, (SFinite.prod finite previous.2).map
        (fun input => input.1 :: input.2) (ListSpace.cons_measurable element)⟩

/-- Ordered iid power, supported on lists of the stated length. -/
@[expose, implicit_reducible] public noncomputable def listPower
    (reference : Measure element) (finite : SFinite reference)
    (count : Nat) : Measure (Space.list element) :=
  (listPowerWithFinite reference finite count).1

@[simp] public theorem listPower_zero
    (reference : Measure element) (finite : SFinite reference) :
    listPower reference finite 0 = Measure.dirac _ [] := rfl

@[simp] public theorem listPower_succ
    (reference : Measure element) (finite : SFinite reference)
    (count : Nat) :
    listPower reference finite (count + 1) =
      (Measure.prod reference (listPower reference finite count)
        (listPowerWithFinite reference finite count).2).map
          (fun input => input.1 :: input.2)
          (ListSpace.cons_measurable element) := rfl

namespace SFinite
/-- Structural s-finiteness of each ordered iid power. -/
public noncomputable def listPower {reference : Measure element}
    (finite : SFinite reference) (count : Nat) :
    SFinite (Measure.listPower reference finite count) :=
  (Measure.listPowerWithFinite reference finite count).2
end SFinite

/-- An iid list power of a probability reference is again a probability law. -/
public theorem IsProbability.listPower {reference : Measure element}
    (probability : IsProbability reference) (finite : SFinite reference)
    (count : Nat) : IsProbability (listPower reference finite count) := by
  induction count with
  | zero =>
      rw [listPower_zero]
      exact IsProbability.dirac _ _
  | succ count induction =>
      rw [listPower_succ]
      apply IsProbability.map
      constructor
      have productUniv :
          (Set.univ : Set (α × List α)) = Set.product Set.univ Set.univ := by
        funext input
        exact propext ⟨fun _ => ⟨True.intro, True.intro⟩,
          fun _ => True.intro⟩
      rw [productUniv, Measure.prod_apply_product _ _ _ element.univ
        (Space.list element).univ, probability.univ_eq_one,
        induction.univ_eq_one, ENNReal.one_mul]

/-- An ordered iid power is supported on lists of its own length. -/
public theorem listPower_length_null (reference : Measure element)
    (finite : SFinite reference) (count : Nat) :
    listPower reference finite count (fun values => values.length ≠ count) =
      ENNReal.zero := by
  have measurable : ∀ length : Nat, (Space.list element).Measurable
      (fun values : List α => values.length ≠ length) :=
    fun length => ListSpace.length_measurable element
      (set := fun value => value ≠ length) trivial
  induction count with
  | zero =>
      rw [listPower_zero, dirac_apply _ _ (measurable 0)]
      exact ite_eq_right (fun different => different rfl)
  | succ count induction =>
      rw [listPower_succ, Measure.map_apply _ _ _ (measurable (count + 1))]
      have product : Set.preimage (fun input : α × List α => input.1 :: input.2)
          (fun values => values.length ≠ count + 1) =
          Set.product Set.univ (fun values : List α => values.length ≠ count) := by
        apply Set.ext
        intro input
        constructor
        · intro different
          exact ⟨True.intro, fun same => different (by
            change input.2.length + 1 = count + 1
            rw [same])⟩
        · rintro ⟨_, different⟩ same
          exact different (Nat.succ.inj same)
      rw [product, Measure.prod_apply_product _ _ _ element.univ (measurable count),
        induction, ENNReal.mul_zero]

private theorem prepend_swap_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.list element) element) (Space.list element)
      (fun input => input.2 :: input.1) :=
  MeasurableMap.comp (ListSpace.cons_measurable element)
    (Space.swap_measurable _ _)

/-- An independent draw inserted at a fixed position `index ≤ count` gives the
next ordered iid power. -/
public theorem insertIdx_power (reference : Measure element)
    (finite : SFinite reference) {count index : Nat} (valid : index ≤ count) :
    (Measure.prod (listPower reference finite count) reference finite).map
        (fun input => input.1.insertIdx index input.2)
        (insert_at_measurable element index) =
      listPower reference finite (count + 1) := by
  induction count generalizing index with
  | zero =>
      have indexZero : index = 0 := Nat.le_zero.mp valid
      subst indexZero
      calc
        _ = (Measure.prod (listPower reference finite 0) reference finite).map
              (fun input => input.2 :: input.1) (prepend_swap_measurable element) :=
          Measure.map_congr_function _ _ _ (funext fun input => List.insertIdx_zero)
        _ = ((Measure.prod (listPower reference finite 0) reference finite).map
              (fun value => (value.2, value.1)) (Space.swap_measurable _ _)).map
              (fun input => input.1 :: input.2) (ListSpace.cons_measurable element) :=
          by rw [Measure.map_comp]
        _ = listPower reference finite 1 := by
          rw [Measure.prod_swap (SFinite.listPower finite 0) finite]
          rfl
  | succ count induction =>
      cases index with
      | zero =>
          calc
            _ = (Measure.prod (listPower reference finite (count + 1)) reference
                  finite).map (fun input => input.2 :: input.1)
                  (prepend_swap_measurable element) :=
              Measure.map_congr_function _ _ _ (funext fun input => List.insertIdx_zero)
            _ = ((Measure.prod (listPower reference finite (count + 1)) reference
                  finite).map (fun value => (value.2, value.1))
                  (Space.swap_measurable _ _)).map
                  (fun input => input.1 :: input.2) (ListSpace.cons_measurable element) :=
              by rw [Measure.map_comp]
            _ = listPower reference finite (count + 1 + 1) := by
              rw [Measure.prod_swap (SFinite.listPower finite (count + 1)) finite]
              rfl
      | succ index =>
          have shorter : index ≤ count := Nat.le_of_succ_le_succ valid
          let previous := listPower reference finite count
          let previousFinite := SFinite.listPower finite count
          have consPair : MeasurableMap
              (Space.product (Space.product element (Space.list element)) element)
              (Space.product (Space.list element) element)
              (fun input => (input.1.1 :: input.1.2, input.2)) :=
            Space.product_map (ListSpace.cons_measurable element)
              (MeasurableMap.identity element)
          have insertTail : MeasurableMap
              (Space.product element (Space.product (Space.list element) element))
              (Space.product element (Space.list element))
              (fun input => (input.1, input.2.1.insertIdx index input.2.2)) :=
            Space.product_map (MeasurableMap.identity element)
              (insert_at_measurable element index)
          calc
            _ = (Measure.prod ((Measure.prod reference previous previousFinite).map
                  (fun input => input.1 :: input.2) (ListSpace.cons_measurable element))
                  reference finite).map
                  (fun input => input.1.insertIdx (index + 1) input.2)
                  (insert_at_measurable element (index + 1)) := rfl
            _ = ((Measure.prod (Measure.prod reference previous previousFinite)
                  reference finite).map
                  (fun input => (input.1.1 :: input.1.2, input.2)) consPair).map
                  (fun input => input.1.insertIdx (index + 1) input.2)
                  (insert_at_measurable element (index + 1)) := by
              rw [Measure.prod_map_left]
            _ = (Measure.prod (Measure.prod reference previous previousFinite)
                  reference finite).map
                  (fun input => (input.1.1 :: input.1.2).insertIdx (index + 1) input.2)
                  (MeasurableMap.comp (insert_at_measurable element (index + 1))
                    consPair) :=
              Measure.map_comp _ _ _ _ _
            _ = ((Measure.prod reference (Measure.prod previous reference finite)
                  (previousFinite.prod finite)).map
                  (fun value => ((value.1, value.2.1), value.2.2))
                  (Space.unassociate_measurable _ _ _)).map
                  (fun input => (input.1.1 :: input.1.2).insertIdx (index + 1) input.2)
                  (MeasurableMap.comp (insert_at_measurable element (index + 1))
                    consPair) := by
              rw [Measure.prod_associate]
            _ = (Measure.prod reference (Measure.prod previous reference finite)
                  (previousFinite.prod finite)).map
                  (fun input => input.1 :: input.2.1.insertIdx index input.2.2)
                  (MeasurableMap.comp (ListSpace.cons_measurable element)
                    insertTail) := by
              rw [Measure.map_comp]
              exact Measure.map_congr_function _ _ _
                (funext fun input => List.insertIdx_succ_cons)
            _ = ((Measure.prod reference (Measure.prod previous reference finite)
                  (previousFinite.prod finite)).map
                  (fun input => (input.1, input.2.1.insertIdx index input.2.2))
                  insertTail).map
                  (fun input => input.1 :: input.2) (ListSpace.cons_measurable element) :=
              by rw [Measure.map_comp]
            _ = (Measure.prod reference ((Measure.prod previous reference finite).map
                  (fun input => input.1.insertIdx index input.2)
                  (insert_at_measurable element index))
                  ((previousFinite.prod finite).map _
                    (insert_at_measurable element index))).map
                  (fun input => input.1 :: input.2) (ListSpace.cons_measurable element) := by
              rw [Measure.prod_map_right]
            _ = (Measure.prod reference (listPower reference finite (count + 1))
                  (SFinite.listPower finite (count + 1))).map
                  (fun input => input.1 :: input.2) (ListSpace.cons_measurable element) := by
              rw [Measure.prod_congr_right reference _ (SFinite.listPower finite (count + 1))
                (induction shorter)]
            _ = listPower reference finite (count + 1 + 1) := rfl


/-- The mass that `uniformBelow bound` gives each position below `bound`. -/
@[expose] public noncomputable def uniformWeight (bound : Nat) : ENNReal :=
  ENNReal.finite (NNReal.div NNReal.one
    (NNReal.ofReal (Problib.Real.Construction.Dedekind.selection.ofRat
      (bound : Rat))))

private theorem partialSum_congr_below {left right : Nat → ENNReal}
    {count : Nat} (equal : ∀ index, index < count → left index = right index) :
    ENNReal.partialSum left count = ENNReal.partialSum right count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [ENNReal.partialSum, ENNReal.partialSum,
        induction (fun index below => equal index (Nat.lt_succ_of_lt below)),
        equal count (Nat.lt_succ_self count)]

/-- `uniformBelow` weighs each position below its bound by `uniformWeight`. -/
public theorem uniformBelow_apply (bound : Nat) (set : Set Nat) :
    uniformBelow bound set = ENNReal.mul (uniformWeight bound)
      (ENNReal.partialSum (fun index =>
        if set index then ENNReal.one else ENNReal.zero) bound) := by
  have measurable : (Space.discrete Nat).Measurable set := trivial
  rw [uniformBelow, Measure.smul_apply_measurable _ _ measurable,
    Measure.sum_apply _ measurable]
  congr 1
  let values : Nat → ENNReal := fun index =>
    (if index < bound then Measure.dirac (Space.discrete Nat) index
      else Measure.zero _) set
  change ENNReal.tsum values = _
  rw [← ENNReal.partialSum_add_tail values bound]
  have tailZero : ENNReal.tsum (fun index => values (bound + index)) =
      ENNReal.zero := by
    rw [ENNReal.tsum_eq_zero_iff]
    intro index
    have outside : ¬ bound + index < bound := by omega
    simp only [values, ite_eq_right outside]
    exact Measure.zero_apply _
  rw [tailZero, ENNReal.add_zero]
  apply partialSum_congr_below
  intro index below
  simp only [values, ite_eq_left below]
  rw [Measure.dirac_apply _ _ measurable]

/-- Sets that agree below the bound have equal `uniformBelow` mass. -/
public theorem uniformBelow_congr {bound : Nat} {left right : Set Nat}
    (equal : ∀ index, index < bound → (left index ↔ right index)) :
    uniformBelow bound left = uniformBelow bound right := by
  rw [uniformBelow_apply, uniformBelow_apply]
  congr 1
  apply partialSum_congr_below
  intro index below
  rw [show left index = right index from propext (equal index below)]

/-- Integration against `uniformBelow` weighs each value below the bound by
`uniformWeight`. -/
public theorem uniformBelow_lintegral (bound : Nat) (function : Nat → ENNReal) :
    lintegral (uniformBelow bound) function =
      ENNReal.mul (uniformWeight bound) (ENNReal.partialSum function bound) := by
  rw [uniformBelow, lintegral_smul_measure, lintegral_sum]
  congr 1
  let values : Nat → ENNReal := fun index =>
    lintegral (if index < bound then Measure.dirac (Space.discrete Nat) index
      else Measure.zero _) function
  change ENNReal.tsum values = _
  rw [← ENNReal.partialSum_add_tail values bound]
  have tailZero : ENNReal.tsum (fun index => values (bound + index)) =
      ENNReal.zero := by
    rw [ENNReal.tsum_eq_zero_iff]
    intro index
    have outside : ¬ bound + index < bound := by omega
    simp only [values, ite_eq_right outside]
    exact lintegral_zero_measure _
  rw [tailZero, ENNReal.add_zero]
  apply partialSum_congr_below
  intro index below
  simp only [values, ite_eq_left below]
  exact lintegral_dirac _ _ (ENNRealMeasurable.of_measurableMap
    (MeasurableMap.from_discrete ennrealBorel function))

/-- Integrands that agree below the bound have equal `uniformBelow`
integrals. -/
public theorem uniformBelow_lintegral_congr {bound : Nat}
    {left right : Nat → ENNReal}
    (equal : ∀ index, index < bound → left index = right index) :
    lintegral (uniformBelow bound) left =
      lintegral (uniformBelow bound) right := by
  rw [uniformBelow_lintegral, uniformBelow_lintegral,
    partialSum_congr_below equal]

/-- Each position below the bound has mass `uniformWeight bound`. -/
public theorem uniformBelow_singleton (bound index : Nat) :
    uniformBelow bound (Set.singleton index) =
      if index < bound then uniformWeight bound else ENNReal.zero := by
  rw [uniformBelow_apply]
  have single : (fun current => if Set.singleton index current then
      ENNReal.one else ENNReal.zero) = ENNReal.single index ENNReal.one := by
    funext current
    by_cases equal : current = index
    · simp [ENNReal.single, Set.singleton, equal]
    · simp [ENNReal.single, Set.singleton, equal]
  rw [single, ENNReal.partialSum_single]
  split
  · exact ENNReal.mul_one _
  · exact ENNReal.mul_zero _

/-- No position at or beyond the bound carries mass. -/
public theorem uniformBelow_outside (bound : Nat) :
    uniformBelow bound (fun index => ¬ index < bound) = ENNReal.zero := by
  rw [uniformBelow_apply]
  refine (congrArg _ ?_).trans (ENNReal.mul_zero _)
  refine (partialSum_congr_below ?_).trans (ENNReal.partialSum_zero bound)
  intro index below
  exact ite_eq_right (Classical.not_not.mpr below)

private theorem partialSum_one (count : Nat) :
    ENNReal.partialSum (fun _ => ENNReal.one) count =
      ENNReal.ofRat (count : Rat) (by exact_mod_cast Nat.zero_le count) := by
  induction count with
  | zero =>
      rw [ENNReal.partialSum]
      exact ENNReal.ofRat_zero.symm
  | succ count induction =>
      rw [ENNReal.partialSum, induction, ← ENNReal.ofRat_one,
        ← ENNReal.ofRat_add]
      congr 1
      push_cast
      rfl

/-- A positive bound makes `uniformBelow` a probability law. -/
public theorem uniformBelow_probability {bound : Nat} (positive : 0 < bound) :
    IsProbability (uniformBelow bound) := by
  constructor
  rw [uniformBelow_apply]
  have all : (fun index => if (Set.univ : Set Nat) index then ENNReal.one
      else ENNReal.zero) = fun _ => ENNReal.one := by
    funext index
    exact ite_eq_left True.intro
  rw [all, partialSum_one, uniformWeight, ENNReal.ofRat,
    ENNReal.finite_mul_finite, NNReal.ofReal_ofRat,
    dite_eq_left (show (0 : Rat) ≤ (bound : Rat) by exact_mod_cast Nat.zero_le bound)]
  have nonzero : NNReal.ofRat (bound : Rat)
      (by exact_mod_cast Nat.zero_le bound) ≠ NNReal.zero := by
    apply (NNReal.zero_lt_iff_ne_zero _).mp
    rw [← NNReal.ofRat_zero]
    exact (NNReal.ofRat_lt_iff 0 (bound : Rat) (by decide)
      (by exact_mod_cast Nat.zero_le bound)).mpr (by exact_mod_cast positive)
  rw [NNReal.div_mul_cancel NNReal.one nonzero]
  rfl

/-- The uniform weight times the bound is one. -/
public theorem uniformWeight_mul_bound {bound : Nat} (positive : 0 < bound) :
    ENNReal.mul (uniformWeight bound)
      (ENNReal.ofRat (bound : Rat) (by exact_mod_cast Nat.zero_le bound)) =
      ENNReal.one := by
  have whole := (uniformBelow_probability positive).univ_eq_one
  rw [uniformBelow_apply] at whole
  have all : (fun index => if (Set.univ : Set Nat) index then ENNReal.one
      else ENNReal.zero) = fun _ => ENNReal.one := by
    funext index
    exact ite_eq_left True.intro
  rw [all, partialSum_one] at whole
  exact whole

private theorem insert_uniform_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.discrete Nat)
        (Space.product (Space.list element) element)) (Space.list element)
      (fun input => input.2.1.insertIdx input.1 input.2.2) :=
  by measurability [insertIdx_measurable element]

/-- A strict birth: an independent draw inserted at a uniform position gives the
next ordered iid power. -/
public theorem insertion_uniform_power (reference : Measure element)
    (finite : SFinite reference) (count : Nat) :
    (Measure.prod (Measure.prod (listPower reference finite count)
        (uniformBelow (count + 1)) (uniformBelowSFinite (count + 1)))
        reference finite).map
      (fun input => input.1.1.insertIdx input.1.2 input.2)
      (insertIdx_measurable element) =
      listPower reference finite (count + 1) := by
  let previous := listPower reference finite count
  let previousFinite := SFinite.listPower finite count
  let positions := uniformBelow (count + 1)
  let positionsFinite := uniformBelowSFinite (count + 1)
  have swapped : Measure.prod previous positions positionsFinite =
      (Measure.prod positions previous previousFinite).map
        (fun value => (value.2, value.1)) (Space.swap_measurable _ _) :=
    (Measure.prod_swap positionsFinite previousFinite).symm
  have regrouped :
      (Measure.prod (Measure.prod previous positions positionsFinite) reference
          finite).map (fun input => input.1.1.insertIdx input.1.2 input.2)
          (insertIdx_measurable element) =
        (Measure.prod positions (Measure.prod previous reference finite)
          (previousFinite.prod finite)).map
          (fun input => input.2.1.insertIdx input.1 input.2.2)
          (insert_uniform_measurable element) := by
    rw [swapped, Measure.prod_map_left, Measure.map_comp,
      Measure.prod_associate, Measure.map_comp]
  change (Measure.prod (Measure.prod previous positions positionsFinite) reference
      finite).map _ _ = _
  rw [regrouped]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable,
    Measure.prod_apply _ _ _ (insert_uniform_measurable element setMeasurable)]
  have inside : ∀ index, index < count + 1 →
      (Measure.prod previous reference finite)
        (Set.preimage (fun value => (index, value))
          (Set.preimage (fun input => input.2.1.insertIdx input.1 input.2.2) set)) =
        listPower reference finite (count + 1) set := by
    intro index below
    rw [← insertIdx_power reference finite (Nat.le_of_lt_succ below),
      Measure.map_apply _ _ _ setMeasurable]
    rfl
  have almost : positions.AEEq
      (fun index => (Measure.prod previous reference finite)
        (Set.preimage (fun value => (index, value))
          (Set.preimage (fun input => input.2.1.insertIdx input.1 input.2.2) set)))
      (fun _ => listPower reference finite (count + 1) set) := by
    refine Measure.NullSet.mono (uniformBelow_outside (count + 1)) ?_
    intro index different
    exact Classical.byContradiction fun outside =>
      different (inside index (Classical.not_not.mp outside))
  rw [lintegral_congr_ae almost, lintegral_const,
    (uniformBelow_probability (Nat.succ_pos count)).univ_eq_one, ENNReal.mul_one]


private theorem prod_length_null (reference : Measure element)
    (finite : SFinite reference) (count : Nat) :
    (Measure.prod reference (listPower reference finite count)
        (SFinite.listPower finite count))
      (Set.complement (fun input : α × List α => input.2.length = count)) =
      ENNReal.zero := by
  have product : Set.complement (fun input : α × List α => input.2.length = count) =
      Set.product Set.univ (fun values : List α => values.length ≠ count) := by
    apply Set.ext
    intro input
    exact ⟨fun different => ⟨True.intro, different⟩, fun member => member.2⟩
  have lengthMeasurable : (Space.list element).Measurable
      (fun values : List α => values.length ≠ count) :=
    ListSpace.length_measurable element (set := fun value => value ≠ count) trivial
  rw [product, Measure.prod_apply_product _ _ _ element.univ lengthMeasurable,
    listPower_length_null, ENNReal.mul_zero]

/-- Reversal preserves every ordered iid power. -/
public theorem listPower_reverse (reference : Measure element)
    (finite : SFinite reference) (count : Nat) :
    (listPower reference finite count).map List.reverse
      (reverse_measurable element) = listPower reference finite count := by
  induction count with
  | zero =>
      rw [listPower_zero, Measure.map_dirac]
      rfl
  | succ count induction =>
      let previous := listPower reference finite count
      let previousFinite := SFinite.listPower finite count
      have reverseTail : MeasurableMap
          (Space.product element (Space.list element))
          (Space.product element (Space.list element))
          (fun input => (input.1, input.2.reverse)) :=
        Space.product_map (MeasurableMap.identity element) (reverse_measurable element)
      have insertLast : MeasurableMap
          (Space.product element (Space.list element)) (Space.list element)
          (fun input => input.2.insertIdx count input.1) :=
        MeasurableMap.comp (insert_at_measurable element count)
          (Space.swap_measurable _ _)
      calc
        _ = (Measure.prod reference previous previousFinite).map
              (fun input => (input.1 :: input.2).reverse)
              (MeasurableMap.comp (reverse_measurable element)
                (ListSpace.cons_measurable element)) := by
          rw [listPower_succ, Measure.map_comp]
          rfl
        _ = (Measure.prod reference previous previousFinite).map
              (fun input => input.2.reverse.insertIdx count input.1)
              (MeasurableMap.comp insertLast reverseTail) := by
          apply Measure.map_congr_on _ (prod_length_null reference finite count)
          intro input same
          change (input.1 :: input.2).reverse =
            input.2.reverse.insertIdx count input.1
          rw [List.reverse_cons, ← same, ← List.length_reverse,
            List.insertIdx_length_self]
        _ = ((Measure.prod reference previous previousFinite).map
              (fun input => (input.1, input.2.reverse)) reverseTail).map
              (fun input => input.2.insertIdx count input.1) insertLast := by
          rw [Measure.map_comp]
        _ = (Measure.prod reference (previous.map List.reverse
              (reverse_measurable element))
              (previousFinite.map List.reverse (reverse_measurable element))).map
              (fun input => input.2.insertIdx count input.1) insertLast := by
          rw [Measure.prod_map_right]
        _ = (Measure.prod reference previous previousFinite).map
              (fun input => input.2.insertIdx count input.1) insertLast := by
          rw [Measure.prod_congr_right reference _ previousFinite induction]
        _ = ((Measure.prod previous reference finite).map
              (fun value => (value.2, value.1)) (Space.swap_measurable _ _)).map
              (fun input => input.2.insertIdx count input.1) insertLast := by
          rw [Measure.prod_swap previousFinite finite]
        _ = listPower reference finite (count + 1) := by
          rw [Measure.map_comp]
          exact insertIdx_power reference finite (Nat.le_refl count)

/-- Independent draws inserted at a valid schedule of positions give the
longer ordered iid power. -/
public theorem insertAll_power (reference : Measure element)
    (finite : SFinite reference) {positions : List Nat} {count : Nat}
    (valid : ValidInsertion positions count) :
    (Measure.prod (listPower reference finite count)
        (listPower reference finite positions.length)
        (SFinite.listPower finite positions.length)).map
      (fun input => insertAll positions input.2 input.1)
      (insertAll_at_measurable element positions) =
      listPower reference finite (count + positions.length) := by
  induction positions generalizing count with
  | nil =>
      calc
        _ = (Measure.prod (listPower reference finite count)
              (listPower reference finite 0) (SFinite.listPower finite 0)).map
              (fun input => input.1) (Space.first_measurable _ _) := rfl
        _ = listPower reference finite count := by
          rw [Measure.prod_map_first, listPower_zero, Measure.dirac_apply_univ,
            Measure.one_smul]
  | cons index rest induction =>
      rcases valid with ⟨below, restValid⟩
      let current := listPower reference finite count
      let currentFinite := SFinite.listPower finite count
      let remaining := listPower reference finite rest.length
      let remainingFinite := SFinite.listPower finite rest.length
      have consRight : MeasurableMap
          (Space.product (Space.list element) (Space.product element (Space.list element)))
          (Space.product (Space.list element) (Space.list element))
          (fun input => (input.1, input.2.1 :: input.2.2)) :=
        Space.product_map (MeasurableMap.identity _) (ListSpace.cons_measurable element)
      have insertLeft : MeasurableMap
          (Space.product (Space.product (Space.list element) element) (Space.list element))
          (Space.product (Space.list element) (Space.list element))
          (fun input => (input.1.1.insertIdx index input.1.2, input.2)) :=
        Space.product_map (insert_at_measurable element index) (MeasurableMap.identity _)
      have lengthEqual : count + 1 + rest.length = count + (rest.length + 1) := by omega
      calc
        _ = (Measure.prod current ((Measure.prod reference remaining
              remainingFinite).map (fun input => input.1 :: input.2)
              (ListSpace.cons_measurable element))
              ((finite.prod remainingFinite).map _
                (ListSpace.cons_measurable element))).map
              (fun input => insertAll (index :: rest) input.2 input.1)
              (insertAll_at_measurable element (index :: rest)) := rfl
        _ = ((Measure.prod current (Measure.prod reference remaining remainingFinite)
              (finite.prod remainingFinite)).map
              (fun input => (input.1, input.2.1 :: input.2.2)) consRight).map
              (fun input => insertAll (index :: rest) input.2 input.1)
              (insertAll_at_measurable element (index :: rest)) := by
          rw [Measure.prod_map_right]
        _ = ((Measure.prod current (Measure.prod reference remaining remainingFinite)
              (finite.prod remainingFinite)).map
              (fun value => ((value.1, value.2.1), value.2.2))
              (Space.unassociate_measurable _ _ _)).map
              (fun input => insertAll rest input.2 (input.1.1.insertIdx index input.1.2))
              (MeasurableMap.comp (insertAll_at_measurable element rest) insertLeft) := by
          rw [Measure.map_comp, Measure.map_comp]
          rfl
        _ = ((Measure.prod (Measure.prod current reference finite) remaining
              remainingFinite).map
              (fun input => (input.1.1.insertIdx index input.1.2, input.2))
              insertLeft).map
              (fun input => insertAll rest input.2 input.1)
              (insertAll_at_measurable element rest) := by
          rw [← Measure.prod_associate, Measure.map_comp]
        _ = (Measure.prod (listPower reference finite (count + 1)) remaining
              remainingFinite).map
              (fun input => insertAll rest input.2 input.1)
              (insertAll_at_measurable element rest) := by
          rw [← Measure.prod_map_left (Measure.prod current reference finite) remaining
            remainingFinite (fun input => input.1.insertIdx index input.2)
            (insert_at_measurable element index),
            insertIdx_power reference finite below]
        _ = listPower reference finite (count + (rest.length + 1)) := by
          rw [induction restValid, lengthEqual]

/-- Removing at a valid schedule of positions splits an ordered iid power into
the remaining power and the power of removed elements. -/
public theorem removeAll_power (reference : Measure element)
    (finite : SFinite reference) {positions : List Nat} {count : Nat}
    (valid : ValidRemoval positions (count + positions.length)) :
    (listPower reference finite (count + positions.length)).map
        (removeAll positions) (removeAll_at_measurable element positions) =
      Measure.prod (listPower reference finite count)
        (listPower reference finite positions.length)
        (SFinite.listPower finite positions.length) := by
  have reversed := insertAll_power reference finite
    (valid_insertion_reverse valid)
  rw [List.length_reverse] at reversed
  let current := listPower reference finite count
  let removed := listPower reference finite positions.length
  let removedFinite := SFinite.listPower finite positions.length
  have reverseSecond : MeasurableMap
      (Space.product (Space.list element) (Space.list element))
      (Space.product (Space.list element) (Space.list element))
      (fun input => (input.1, input.2.reverse)) :=
    Space.product_map (MeasurableMap.identity _) (reverse_measurable element)
  have region : (Measure.prod current removed removedFinite)
      (Set.complement (fun input : List α × List α =>
        input.1.length = count ∧ input.2.length = positions.length)) =
      ENNReal.zero := by
    have lengthMeasurable : ∀ length : Nat, (Space.list element).Measurable
        (fun values : List α => values.length ≠ length) :=
      fun length => ListSpace.length_measurable element
        (set := fun value => value ≠ length) trivial
    have first : (Measure.prod current removed removedFinite)
        (Set.product (fun values : List α => values.length ≠ count) Set.univ) =
        ENNReal.zero := by
      rw [Measure.prod_apply_product _ _ _ (lengthMeasurable count) (Space.list element).univ,
        listPower_length_null, ENNReal.zero_mul]
    have second : (Measure.prod current removed removedFinite)
        (Set.product Set.univ (fun values : List α => values.length ≠ positions.length)) =
        ENNReal.zero := by
      rw [Measure.prod_apply_product _ _ _ (Space.list element).univ
        (lengthMeasurable positions.length), listPower_length_null, ENNReal.mul_zero]
    apply Measure.NullSet.mono (Measure.NullSet.union first second)
    intro input outside
    by_cases same : input.1.length = count
    · exact Or.inr ⟨True.intro, fun other => outside ⟨same, other⟩⟩
    · exact Or.inl ⟨same, True.intro⟩
  calc
    _ = ((Measure.prod current removed removedFinite).map
          (fun input => insertAll positions.reverse input.2 input.1)
          (insertAll_at_measurable element positions.reverse)).map
          (removeAll positions) (removeAll_at_measurable element positions) := by
      rw [reversed]
    _ = (Measure.prod current removed removedFinite).map
          (fun input => (input.1, input.2.reverse)) reverseSecond := by
      rw [Measure.map_comp]
      apply Measure.map_congr_on _ region
      intro input lengths
      have restored := removeAll_insertAll (positions := positions.reverse)
        (inserted := input.2) (values := input.1)
        (by rw [lengths.1]; exact valid_insertion_reverse valid)
        (by rw [lengths.2, List.length_reverse])
      rw [List.reverse_reverse] at restored
      exact restored
    _ = Measure.prod current (removed.map List.reverse (reverse_measurable element))
          (removedFinite.map List.reverse (reverse_measurable element)) := by
      rw [Measure.prod_map_right]
    _ = Measure.prod current removed removedFinite :=
      Measure.prod_congr_right current _ removedFinite
        (listPower_reverse reference finite positions.length)

end Measure
end
end Problib.Measure
