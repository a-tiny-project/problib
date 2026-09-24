module

public import Problib.Measure.Giry.Basic
public import Problib.Real.Extended.Lattice
public import Problib.Measure.Decomposition.Hahn.Existence
public import Problib.Measure.Additive.Subtract
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

namespace Problib.Measure.Giry.Law

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- Total variation of probability laws, measured by the largest difference
in mass assigned to a measurable event. -/
@[expose] public noncomputable def totalVariation (μ ν : Giry.Law space) : ENNReal :=
  ENNReal.supremum (fun distance =>
    ∃ event : Set α, space.Measurable event ∧
      distance = ENNReal.max
        (ENNReal.sub (μ.val event) (ν.val event))
        (ENNReal.sub (ν.val event) (μ.val event)))

private theorem max_comm (left right : ENNReal) :
    ENNReal.max left right = ENNReal.max right left := by
  rcases ENNReal.le_total left right with included | included
  · rw [ENNReal.max_eq_right included, ENNReal.max_eq_left included]
  · rw [ENNReal.max_eq_left included, ENNReal.max_eq_right included]

/-- The difference of the two event masses is bounded by total variation. -/
public theorem event_sub_le (μ ν : Giry.Law space) {event : Set α}
    (measurable : space.Measurable event) :
    ENNReal.le (ENNReal.sub (μ.val event) (ν.val event))
      (totalVariation μ ν) :=
  ENNReal.le_trans (ENNReal.le_max_left _ _)
    (ENNReal.le_supremum ⟨event, measurable, rfl⟩)

/-- Total variation between probability laws never exceeds one. -/
public theorem totalVariation_le_one (μ ν : Giry.Law space) :
    ENNReal.le (totalVariation μ ν) ENNReal.one := by
  apply ENNReal.supremum_le
  rintro distance ⟨event, _, rfl⟩
  apply ENNReal.max_le
  · exact ENNReal.le_trans (ENNReal.sub_le_self _ _) (μ.property.apply_le_one event)
  · exact ENNReal.le_trans (ENNReal.sub_le_self _ _) (ν.property.apply_le_one event)

/-- A probability law has zero total variation from itself. -/
public theorem totalVariation_self (μ : Giry.Law space) :
    totalVariation μ μ = ENNReal.zero := by
  apply ENNReal.supremum_eq_zero_iff.mpr
  rintro distance ⟨event, _, rfl⟩
  rw [ENNReal.sub_self, ENNReal.max_eq_right (ENNReal.le_refl _)]

/-- Total variation is symmetric. -/
public theorem totalVariation_symm (μ ν : Giry.Law space) :
    totalVariation μ ν = totalVariation ν μ := by
  unfold totalVariation
  apply congrArg ENNReal.supremum
  funext distance
  apply propext
  constructor
  · rintro ⟨event, measurable, rfl⟩
    exact ⟨event, measurable, max_comm _ _⟩
  · rintro ⟨event, measurable, rfl⟩
    exact ⟨event, measurable, max_comm _ _⟩

/-- Zero total variation characterizes equality of probability laws. -/
public theorem totalVariation_eq_zero_iff (μ ν : Giry.Law space) :
    totalVariation μ ν = ENNReal.zero ↔ μ = ν := by
  constructor
  · intro zero
    apply Giry.ext
    intro event measurable
    have forward := event_sub_le μ ν measurable
    rw [zero] at forward
    have backward := event_sub_le ν μ measurable
    rw [← totalVariation_symm μ ν, zero] at backward
    exact ENNReal.le_antisymm
      (ENNReal.sub_eq_zero_iff_le.mp (ENNReal.eq_zero_of_le_zero forward))
      (ENNReal.sub_eq_zero_iff_le.mp (ENNReal.eq_zero_of_le_zero backward))
  · intro equal
    subst ν
    exact totalVariation_self μ

/-- Total variation obeys the triangle inequality. -/
public theorem totalVariation_triangle (μ ν ρ : Giry.Law space) :
    ENNReal.le (totalVariation μ ρ)
      (ENNReal.add (totalVariation μ ν) (totalVariation ν ρ)) := by
  apply ENNReal.supremum_le
  rintro distance ⟨event, measurable, rfl⟩
  have difference (left middle right : ENNReal) :
      ENNReal.le (ENNReal.sub left right)
        (ENNReal.add (ENNReal.sub left middle) (ENNReal.sub middle right)) := by
    apply ENNReal.sub_le_iff_le_add.mpr
    have first := ENNReal.le_sub_add left middle
    have second := ENNReal.le_sub_add middle right
    have chain := ENNReal.le_trans first
      (ENNReal.add_le_add_left second (ENNReal.sub left middle))
    simpa only [ENNReal.add_assoc] using chain
  apply ENNReal.max_le
  · exact ENNReal.le_trans
      (difference (μ.val event) (ν.val event) (ρ.val event))
      (ENNReal.add_le_add (event_sub_le μ ν measurable)
        (event_sub_le ν ρ measurable))
  · have bound := ENNReal.add_le_add
      (event_sub_le ρ ν measurable) (event_sub_le ν μ measurable)
    have bound' : ENNReal.le
        (ENNReal.add
          (ENNReal.sub (ρ.val event) (ν.val event))
          (ENNReal.sub (ν.val event) (μ.val event)))
        (ENNReal.add (totalVariation μ ν) (totalVariation ν ρ)) := by
      simpa only [totalVariation_symm ρ ν, totalVariation_symm ν μ,
        ENNReal.add_comm (totalVariation ν ρ) (totalVariation μ ν)] using bound
    exact ENNReal.le_trans
      (difference (ρ.val event) (ν.val event) (μ.val event)) bound'

/-- The integral difference of a bounded nonnegative function scales with
the largest possible event-mass difference. -/
public theorem lintegral_sub_le_scaled_totalVariation (μ ν : Giry.Law space)
    {function : α → ENNReal}
    (_measurable : ENNRealMeasurable space function)
    (upper : ENNReal)
    (bounded : ∀ input, ENNReal.le (function input) upper) :
    ENNReal.le
      (ENNReal.sub (lintegral μ.val function) (lintegral ν.val function))
      (ENNReal.mul upper (totalVariation μ ν)) := by
  let hahn := Measure.HahnDecomposition.ofFinite μ.property.to_finite
    ν.property.to_finite
  let positive := μ.val.restrict hahn.region
  let negative := μ.val.restrict (Set.complement hahn.region)
  let common := ν.val.restrict hahn.region
  let other := ν.val.restrict (Set.complement hahn.region)
  have included : ∀ event, space.Measurable event →
      ENNReal.le (common event) (positive event) := by
    intro event eventMeasurable
    change ENNReal.le ((ν.val.restrict hahn.region) event)
      ((μ.val.restrict hahn.region) event)
    rw [Measure.restrict_apply _ _ eventMeasurable,
      Measure.restrict_apply _ _ eventMeasurable]
    exact hahn.positive (space.inter eventMeasurable hahn.measurable)
      (fun {_} member => member.2)
  have negativeIncluded : ∀ event, space.Measurable event →
      ENNReal.le (negative event) (other event) := by
    intro event eventMeasurable
    change ENNReal.le ((μ.val.restrict (Set.complement hahn.region)) event)
      ((ν.val.restrict (Set.complement hahn.region)) event)
    rw [Measure.restrict_apply _ _ eventMeasurable,
      Measure.restrict_apply _ _ eventMeasurable]
    exact hahn.negative
      (space.inter eventMeasurable (space.complement hahn.measurable))
      (fun {_} member => member.2)
  let residual := Measure.subtract (ν.property.to_finite.restrict hahn.region) included
  have reconstruct : Measure.add residual common = positive :=
    Measure.subtract_add (ν.property.to_finite.restrict hahn.region) included
  have leftSplit := Measure.restrict_add_complement μ.val hahn.measurable
  have rightSplit := Measure.restrict_add_complement ν.val hahn.measurable
  have leftIntegral : lintegral μ.val function =
      ENNReal.add (lintegral residual function)
        (ENNReal.add (lintegral common function)
          (lintegral negative function)) := by
    calc
      lintegral μ.val function =
          lintegral (Measure.add positive negative) function := by rw [leftSplit]
      _ = ENNReal.add (lintegral positive function)
          (lintegral negative function) := lintegral_add_measure function positive negative
      _ = ENNReal.add
          (ENNReal.add (lintegral residual function) (lintegral common function))
          (lintegral negative function) := by rw [← reconstruct, lintegral_add_measure]
      _ = ENNReal.add (lintegral residual function)
          (ENNReal.add (lintegral common function)
            (lintegral negative function)) := ENNReal.add_assoc _ _ _
  have rightIntegral : lintegral ν.val function =
      ENNReal.add (lintegral common function)
        (lintegral other function) := by
    rw [← rightSplit, lintegral_add_measure]
  have negativeIntegral :=
    lintegral_mono_measure function negative other negativeIncluded
  have integralBound : ENNReal.le (lintegral μ.val function)
      (ENNReal.add (lintegral residual function)
        (lintegral ν.val function)) := by
    rw [leftIntegral, rightIntegral]
    exact ENNReal.add_le_add_left
      (ENNReal.add_le_add_left negativeIntegral _) _
  have differenceBound := ENNReal.sub_le_iff_le_add.mpr integralBound
  have residualBound : ENNReal.le (lintegral residual function)
      (ENNReal.mul upper (residual Set.univ)) := by
    have comparison := lintegral_mono residual bounded
    rw [lintegral_const] at comparison
    exact comparison
  have residualMass : residual Set.univ =
      ENNReal.sub (μ.val hahn.region) (ν.val hahn.region) := by
    rw [Measure.subtract_apply (ν.property.to_finite.restrict hahn.region)
      included space.univ, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  exact ENNReal.le_trans differenceBound
    (ENNReal.le_trans residualBound
      (by
        rw [residualMass]
        exact ENNReal.mul_le_mul_left
          (event_sub_le μ ν hahn.measurable) upper))

/-- A measurable unit-bounded function has no larger one-sided integral
difference than the total variation of the two laws. -/
public theorem lintegral_sub_le_totalVariation (μ ν : Giry.Law space)
    {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function)
    (bounded : ∀ input, ENNReal.le (function input) ENNReal.one) :
    ENNReal.le
      (ENNReal.sub (lintegral μ.val function) (lintegral ν.val function))
      (totalVariation μ ν) := by
  have scaled := lintegral_sub_le_scaled_totalVariation μ ν measurable
    ENNReal.one bounded
  rwa [ENNReal.one_mul] at scaled

/-- The same bound holds for the absolute integral difference. -/
public theorem lintegral_distance_le_totalVariation (μ ν : Giry.Law space)
    {function : α → ENNReal}
    (measurable : ENNRealMeasurable space function)
    (bounded : ∀ input, ENNReal.le (function input) ENNReal.one) :
    ENNReal.le
      (ENNReal.max
        (ENNReal.sub (lintegral μ.val function) (lintegral ν.val function))
        (ENNReal.sub (lintegral ν.val function) (lintegral μ.val function)))
      (totalVariation μ ν) := by
  apply ENNReal.max_le
  · exact lintegral_sub_le_totalVariation μ ν measurable bounded
  · rw [totalVariation_symm μ ν]
    exact lintegral_sub_le_totalVariation ν μ measurable bounded

/-- Total variation also is the largest integral difference of a measurable
function with values in the unit interval. -/
public theorem totalVariation_eq_sup_lintegral (μ ν : Giry.Law space) :
    totalVariation μ ν = ENNReal.supremum (fun distance =>
      ∃ function : α → ENNReal,
        ENNRealMeasurable space function ∧
        (∀ input, ENNReal.le (function input) ENNReal.one) ∧
        distance = ENNReal.max
          (ENNReal.sub (lintegral μ.val function) (lintegral ν.val function))
          (ENNReal.sub (lintegral ν.val function) (lintegral μ.val function))) := by
  apply ENNReal.le_antisymm
  · apply ENNReal.supremum_le
    rintro distance ⟨event, eventMeasurable, rfl⟩
    let function := ennrealIndicator event (fun _ : α => ENNReal.one)
    have functionMeasurable : ENNRealMeasurable space function :=
      ENNRealMeasurable.indicator eventMeasurable
        (ENNRealMeasurable.constant space ENNReal.one)
    have functionBound : ∀ input, ENNReal.le (function input) ENNReal.one := by
      intro input
      classical
      by_cases member : event input
      · simp only [function, ennrealIndicator, ennrealPiecewise, if_pos member]
        exact ENNReal.le_refl _
      · simp only [function, ennrealIndicator, ennrealPiecewise, if_neg member]
        exact ENNReal.zero_le _
    have leftIntegral : lintegral μ.val function = μ.val event := by
      exact (apply_eq_lintegral_indicator μ.val eventMeasurable).symm
    have rightIntegral : lintegral ν.val function = ν.val event := by
      exact (apply_eq_lintegral_indicator ν.val eventMeasurable).symm
    rw [← leftIntegral, ← rightIntegral]
    exact ENNReal.le_supremum ⟨function, functionMeasurable, functionBound, rfl⟩
  · apply ENNReal.supremum_le
    rintro distance ⟨function, functionMeasurable, functionBound, rfl⟩
    exact lintegral_distance_le_totalVariation μ ν functionMeasurable functionBound

end Problib.Measure.Giry.Law
