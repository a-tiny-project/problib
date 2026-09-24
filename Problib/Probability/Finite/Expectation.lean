import Problib.Probability.Finite.PMF

namespace Problib.Probability

universe u v

private def expectationWeights {α : Type u} (observable : α → Rat) :
    List (α × NNRat) → Rat
  | [] => 0
  | (value, weight) :: rest =>
      (weight : Rat) * observable value + expectationWeights observable rest

private theorem expectationWeights_congr {α : Type u} (weights : List (α × NNRat))
    {left right : α → Rat} (equal : ∀ value, left value = right value) :
    expectationWeights left weights = expectationWeights right weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [expectationWeights]
          rw [equal value, ih]

private theorem expectationWeights_zero {α : Type u} (weights : List (α × NNRat)) :
    expectationWeights (fun _ => 0) weights = 0 := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      rw [expectationWeights, Rat.mul_zero, ih, Rat.zero_add]

private theorem expectationWeights_add {α : Type u} (weights : List (α × NNRat))
    (left right : α → Rat) :
    expectationWeights (fun value => left value + right value) weights =
      expectationWeights left weights + expectationWeights right weights := by
  induction weights with
  | nil =>
      change (0 : Rat) = 0 + 0
      rw [Rat.zero_add]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [expectationWeights]
          rw [Rat.mul_add, ih]
          calc
            (weight : Rat) * left value + (weight : Rat) * right value +
                (expectationWeights left tail + expectationWeights right tail) =
                (weight : Rat) * left value +
                  ((weight : Rat) * right value +
                    (expectationWeights left tail + expectationWeights right tail)) :=
              Rat.add_assoc _ _ _
            _ = (weight : Rat) * left value +
                (expectationWeights left tail +
                  ((weight : Rat) * right value + expectationWeights right tail)) := by
              rw [Rat.add_left_comm ((weight : Rat) * right value)
                (expectationWeights left tail) (expectationWeights right tail)]
            _ = ((weight : Rat) * left value + expectationWeights left tail) +
                ((weight : Rat) * right value + expectationWeights right tail) :=
              (Rat.add_assoc _ _ _).symm
            _ = _ := rfl

private theorem expectationWeights_scale {α : Type u} (weights : List (α × NNRat))
    (constant : Rat) (observable : α → Rat) :
    expectationWeights (fun value => constant * observable value) weights =
      constant * expectationWeights observable weights := by
  induction weights with
  | nil => simp [expectationWeights]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [expectationWeights]
          rw [ih, Rat.mul_add]
          have headEqual : (weight : Rat) * (constant * observable value) =
              constant * ((weight : Rat) * observable value) := by
            rw [← Rat.mul_assoc, Rat.mul_comm (weight : Rat) constant, Rat.mul_assoc]
          rw [headEqual]

private def positivePart (value : Rat) : NNRat :=
  if nonnegative : 0 ≤ value then NNRat.ofRat value nonnegative else 0

private theorem positivePart_sub_negative_part (value : Rat) :
    (positivePart value : Rat) - (positivePart (-value) : Rat) = value := by
  by_cases nonnegative : 0 ≤ value
  · by_cases negativeNonnegative : 0 ≤ -value
    · have nonpositive : value ≤ 0 := by
        have negated := Rat.neg_le_neg negativeNonnegative
        simpa using negated
      have zero : value = 0 := Rat.le_antisymm nonpositive nonnegative
      subst value
      simp [positivePart, NNRat.ofRat, Rat.sub_eq_add_neg]
      rw [Rat.zero_add]
    · simp [positivePart, NNRat.ofRat, nonnegative, negativeNonnegative,
        Rat.sub_eq_add_neg]
      rw [Rat.add_zero]
  · have negativeNonnegative : 0 ≤ -value := by
      have negative := Rat.not_le.mp nonnegative
      have negated := Rat.neg_lt_neg negative
      exact Rat.le_of_lt (by simpa using negated)
    simp [positivePart, NNRat.ofRat, nonnegative, negativeNonnegative,
      Rat.sub_eq_add_neg]
    rw [Rat.zero_add]

namespace FiniteMeasure

def expectation {α : Type u} (measure : FiniteMeasure α) (observable : α → Rat) : Rat :=
  expectationWeights observable measure.weights

theorem expectation_map {α : Type u} {β : Type v}
    (transform : α → β) (measure : FiniteMeasure α) (observable : β → Rat) :
    (map transform measure).expectation observable =
      measure.expectation (fun value => observable (transform value)) := by
  cases measure with
  | mk weights =>
      induction weights with
      | nil => rfl
      | cons head tail induction =>
          cases head with
          | mk value weight =>
              change (weight : Rat) * observable (transform value) +
                    (map transform (FiniteMeasure.mk tail)).expectation observable =
                  (weight : Rat) * observable (transform value) +
                    (FiniteMeasure.mk tail).expectation
                      (fun next => observable (transform next))
              exact congrArg
                (fun rest : Rat =>
                  (weight : Rat) * observable (transform value) + rest)
                induction

@[simp] theorem expectation_weights_nil {α : Type u} (observable : α → Rat) :
    (FiniteMeasure.mk []).expectation observable = 0 :=
  rfl

@[simp] theorem expectation_weights_cons {α : Type u} (value : α)
    (weight : NNRat) (weights : List (α × NNRat)) (observable : α → Rat) :
    (FiniteMeasure.mk ((value, weight) :: weights)).expectation observable =
      (weight : Rat) * observable value +
        (FiniteMeasure.mk weights).expectation observable :=
  rfl

@[simp] theorem expectation_zero {α : Type u} (measure : FiniteMeasure α) :
    measure.expectation (fun _ => 0) = 0 :=
  expectationWeights_zero measure.weights

@[simp] theorem expectation_dirac {α : Type u} (value : α) (observable : α → Rat) :
    (dirac value).expectation observable = observable value := by
  change (1 : Rat) * observable value + 0 = observable value
  rw [Rat.one_mul, Rat.add_zero]

theorem expectation_congr {α : Type u} (measure : FiniteMeasure α)
    {left right : α → Rat} (equal : ∀ value, left value = right value) :
    measure.expectation left = measure.expectation right :=
  expectationWeights_congr measure.weights equal

theorem expectation_add {α : Type u} (measure : FiniteMeasure α)
    (left right : α → Rat) :
    measure.expectation (fun value => left value + right value) =
      measure.expectation left + measure.expectation right :=
  expectationWeights_add measure.weights left right

theorem expectation_scale {α : Type u} (measure : FiniteMeasure α)
    (constant : Rat) (observable : α → Rat) :
    measure.expectation (fun value => constant * observable value) =
      constant * measure.expectation observable :=
  expectationWeights_scale measure.weights constant observable

theorem expectation_coe_integral {α : Type u} (measure : FiniteMeasure α)
    (observable : α → NNRat) :
    measure.expectation (fun value => (observable value : Rat)) =
      (measure.integral observable : Rat) := by
  cases measure with
  | mk weights =>
      induction weights with
      | nil => rfl
      | cons head tail induction =>
          cases head with
          | mk value weight =>
              change (weight : Rat) * (observable value : Rat) +
                    (FiniteMeasure.mk tail).expectation
                      (fun next => (observable next : Rat)) =
                ((weight * observable value : NNRat) +
                  (FiniteMeasure.mk tail).integral observable : NNRat)
              rw [induction]
              rfl

theorem expectation_neg {α : Type u} (measure : FiniteMeasure α)
    (observable : α → Rat) :
    measure.expectation (fun value => -observable value) =
      -measure.expectation observable := by
  calc
    measure.expectation (fun value => -observable value) =
        measure.expectation (fun value => (-1 : Rat) * observable value) := by
      apply expectation_congr
      intro value
      rw [Rat.neg_mul, Rat.one_mul]
    _ = (-1 : Rat) * measure.expectation observable :=
      expectation_scale measure (-1) observable
    _ = -measure.expectation observable := by
      rw [Rat.neg_mul, Rat.one_mul]

theorem expectation_sub {α : Type u} (measure : FiniteMeasure α)
    (left right : α → Rat) :
    measure.expectation (fun value => left value - right value) =
      measure.expectation left - measure.expectation right := by
  rw [show (fun value => left value - right value) =
      (fun value => left value + -right value) by
        funext value
        exact Rat.sub_eq_add_neg _ _]
  rw [expectation_add, expectation_neg, Rat.sub_eq_add_neg]

theorem Equivalent.expectation_eq {α : Type u} {left right : FiniteMeasure α}
    (equivalent : left ≈ₘ right) (observable : α → Rat) :
    left.expectation observable = right.expectation observable := by
  let positive : α → NNRat := fun value => positivePart (observable value)
  let negative : α → NNRat := fun value => positivePart (-observable value)
  calc
    left.expectation observable =
        left.expectation (fun value =>
          (positive value : Rat) - (negative value : Rat)) := by
      apply expectation_congr
      intro value
      exact (positivePart_sub_negative_part (observable value)).symm
    _ = left.expectation (fun value => (positive value : Rat)) -
          left.expectation (fun value => (negative value : Rat)) :=
      expectation_sub left _ _
    _ = (left.integral positive : Rat) - (left.integral negative : Rat) := by
      rw [expectation_coe_integral, expectation_coe_integral]
    _ = (right.integral positive : Rat) - (right.integral negative : Rat) := by
      rw [equivalent positive, equivalent negative]
    _ = right.expectation (fun value => (positive value : Rat)) -
          right.expectation (fun value => (negative value : Rat)) := by
      rw [expectation_coe_integral, expectation_coe_integral]
    _ = right.expectation (fun value =>
          (positive value : Rat) - (negative value : Rat)) :=
      (expectation_sub right _ _).symm
    _ = right.expectation observable := by
      apply expectation_congr
      intro value
      exact positivePart_sub_negative_part (observable value)

end FiniteMeasure

namespace FinitePMF

def expectation {α : Type u} (pmf : FinitePMF α) (observable : α → Rat) : Rat :=
  pmf.measure.expectation observable

theorem expectation_map {α : Type u} {β : Type v}
    (transform : α → β) (pmf : FinitePMF α) (observable : β → Rat) :
    (map transform pmf).expectation observable =
      pmf.expectation (fun value => observable (transform value)) :=
  FiniteMeasure.expectation_map transform pmf.measure observable

@[simp] theorem expectation_zero {α : Type u} (pmf : FinitePMF α) :
    pmf.expectation (fun _ => 0) = 0 :=
  FiniteMeasure.expectation_zero pmf.measure

@[simp] theorem expectation_dirac {α : Type u} (value : α) (observable : α → Rat) :
    (dirac value).expectation observable = observable value :=
  FiniteMeasure.expectation_dirac value observable

theorem expectation_congr {α : Type u} (pmf : FinitePMF α)
    {left right : α → Rat} (equal : ∀ value, left value = right value) :
    pmf.expectation left = pmf.expectation right :=
  FiniteMeasure.expectation_congr pmf.measure equal

theorem expectation_add {α : Type u} (pmf : FinitePMF α)
    (left right : α → Rat) :
    pmf.expectation (fun value => left value + right value) =
      pmf.expectation left + pmf.expectation right :=
  FiniteMeasure.expectation_add pmf.measure left right

theorem expectation_scale {α : Type u} (pmf : FinitePMF α)
    (constant : Rat) (observable : α → Rat) :
    pmf.expectation (fun value => constant * observable value) =
      constant * pmf.expectation observable :=
  FiniteMeasure.expectation_scale pmf.measure constant observable

theorem Equivalent.expectation_eq {α : Type u} {left right : FinitePMF α}
    (equivalent : left ≈ₚ right) (observable : α → Rat) :
    left.expectation observable = right.expectation observable :=
  FiniteMeasure.Equivalent.expectation_eq equivalent observable

end FinitePMF

end Problib.Probability
