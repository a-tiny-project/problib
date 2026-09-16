import Foundations.Probability.Finite.PMF

namespace Foundations.Probability

universe u v

namespace FiniteMeasure

private def countingList {α : Type u} : List α → FiniteMeasure α
  | [] => 0
  | value :: rest => dirac value + countingList rest

def counting {α : Type u} [DecidableEq α] (set : FiniteSet α) : FiniteMeasure α :=
  countingList set.elements

private theorem mass_countingList {α : Type u} [DecidableEq α]
    (values : List α) (nodup : values.Nodup) (point : α) :
    (countingList values).mass point = if point ∈ values then 1 else 0 := by
  induction values with
  | nil => simp [countingList]
  | cons value rest ih =>
      have facts := List.nodup_cons.1 nodup
      by_cases equal : value = point
      · subst equal
        simp [countingList, mass_add, mass_dirac, ih facts.2, facts.1]
      · have reverseUnequal : point ≠ value := by
          intro reverseEqual
          exact equal reverseEqual.symm
        simp [countingList, mass_add, mass_dirac, equal, reverseUnequal, ih facts.2]

theorem mass_counting {α : Type u} [DecidableEq α] (set : FiniteSet α) (point : α) :
    (counting set).mass point = if point ∈ set then 1 else 0 :=
  mass_countingList set.elements set.nodup point

def AbsolutelyContinuous {α : Type u} [DecidableEq α]
    (measure reference : FiniteMeasure α) : Prop :=
  ∀ point, reference.mass point = 0 → measure.mass point = 0

def IsDensity {α : Type u} [DecidableEq α]
    (measure reference : FiniteMeasure α) (density : α → NNRat) : Prop :=
  ∀ point, measure.mass point = reference.mass point * density point

def withDensity {α : Type u} (reference : FiniteMeasure α)
    (density : α → NNRat) : FiniteMeasure α :=
  reference.reweight density

theorem withDensity_isDensity {α : Type u} [DecidableEq α]
    (reference : FiniteMeasure α) (density : α → NNRat) :
    IsDensity (withDensity reference density) reference density := by
  intro point
  exact mass_reweight reference density point

theorem IsDensity.reference_equivalent {α : Type u} [DecidableEq α]
    {measure reference otherReference : FiniteMeasure α} {density : α → NNRat}
    (hasDensity : IsDensity measure reference density)
    (equivalent : otherReference ≈ₘ reference) :
    IsDensity measure otherReference density := by
  intro point
  rw [equivalent.mass_eq point]
  exact hasDensity point

theorem IsDensity.measure_equivalent {α : Type u} [DecidableEq α]
    {measure otherMeasure reference : FiniteMeasure α} {density : α → NNRat}
    (hasDensity : IsDensity measure reference density)
    (equivalent : otherMeasure ≈ₘ measure) :
    IsDensity otherMeasure reference density := by
  intro point
  rw [equivalent.mass_eq point]
  exact hasDensity point

theorem reweight_isDensity {α : Type u} [DecidableEq α]
    {measure reference : FiniteMeasure α} {density : α → NNRat}
    (hasDensity : IsDensity measure reference density) (factor : α → NNRat) :
    IsDensity (measure.reweight factor) reference
      (fun point => density point * factor point) := by
  intro point
  rw [mass_reweight, hasDensity point, NNRat.mul_assoc]

theorem bind_isDensity {α : Type u} {β : Type v} [DecidableEq β]
    (measure : FiniteMeasure α) (kernel : α → FiniteMeasure β)
    (reference : FiniteMeasure β) (density : α → β → NNRat)
    (kernelDensity : ∀ value, IsDensity (kernel value) reference (density value)) :
    IsDensity (measure.bind kernel) reference
      (fun point => measure.integral fun value => density value point) := by
  intro point
  rw [mass_bind]
  calc
    measure.integral (fun value => (kernel value).mass point) =
        measure.integral (fun value => reference.mass point * density value point) := by
          apply integral_congr
          intro value
          exact kernelDensity value point
    _ = reference.mass point * measure.integral (fun value => density value point) :=
      integral_mul_left measure (reference.mass point) fun value => density value point

theorem IsDensity.absolutelyContinuous {α : Type u} [DecidableEq α]
    {measure reference : FiniteMeasure α} {density : α → NNRat}
    (hasDensity : IsDensity measure reference density) :
    AbsolutelyContinuous measure reference := by
  intro point referenceZero
  rw [hasDensity point, referenceZero, NNRat.zero_mul]

theorem absolutelyContinuous_refl {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) : AbsolutelyContinuous measure measure := by
  intro point zeroMass
  exact zeroMass

theorem absolutelyContinuous_trans {α : Type u} [DecidableEq α]
    {first second third : FiniteMeasure α}
    (firstSecond : AbsolutelyContinuous first second)
    (secondThird : AbsolutelyContinuous second third) :
    AbsolutelyContinuous first third := by
  intro point thirdZero
  exact firstSecond point (secondThird point thirdZero)

def densityOf {α : Type u} [DecidableEq α]
    (measure reference : FiniteMeasure α) (point : α) : NNRat :=
  if zeroReference : reference.mass point = 0 then
    0
  else
    NNRat.inverse (reference.mass point) zeroReference * measure.mass point

theorem densityOf_isDensity {α : Type u} [DecidableEq α]
    {measure reference : FiniteMeasure α}
    (absoluteContinuity : AbsolutelyContinuous measure reference) :
    IsDensity measure reference (densityOf measure reference) := by
  intro point
  by_cases zeroReference : reference.mass point = 0
  · simp [densityOf, zeroReference, absoluteContinuity point zeroReference]
  · rw [densityOf, dif_neg zeroReference]
    calc
      measure.mass point = 1 * measure.mass point := (NNRat.one_mul _).symm
      _ = (reference.mass point * NNRat.inverse (reference.mass point) zeroReference) *
          measure.mass point := by rw [NNRat.mul_inverse_self]
      _ = reference.mass point *
          (NNRat.inverse (reference.mass point) zeroReference * measure.mass point) :=
            NNRat.mul_assoc _ _ _

theorem absolutelyContinuous_iff_density {α : Type u} [DecidableEq α]
    (measure reference : FiniteMeasure α) :
    AbsolutelyContinuous measure reference ↔
      ∃ density, IsDensity measure reference density := by
  constructor
  · intro absoluteContinuity
    exact ⟨densityOf measure reference, densityOf_isDensity absoluteContinuity⟩
  · intro existsDensity
    cases existsDensity with
    | intro density hasDensity => exact hasDensity.absolutelyContinuous

def supportCounting {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) : FiniteMeasure α :=
  counting measure.support

theorem support_isDensity {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) :
    IsDensity measure (supportCounting measure) measure.mass := by
  intro point
  by_cases present : point ∈ measure.support
  · simp [supportCounting, mass_counting, present]
  · have zeroMass := mass_zero_outside_support measure point present
    simp [supportCounting, mass_counting, present, zeroMass]

theorem support_absolutelyContinuous {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) :
    AbsolutelyContinuous measure (supportCounting measure) :=
  (support_isDensity measure).absolutelyContinuous

def densitySimulation {α : Type u} (measure : FiniteMeasure α)
    (density : α → NNRat) : FiniteMeasure (α × NNRat) :=
  measure.map fun value => (value, density value)

def IsDensitySimulation {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (density : α → NNRat)
    (output : FiniteMeasure (α × NNRat)) : Prop :=
  output.map Prod.fst ≈ₘ measure ∧
    (∀ point, output.mass (point, density point) = measure.mass point) ∧
    ∀ point reported, reported ≠ density point → output.mass (point, reported) = 0

theorem densitySimulation_value_marginal {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (density : α → NNRat) :
    (densitySimulation measure density).map Prod.fst ≈ₘ measure := by
  exact Equivalent.trans
    (map_comp (fun value => (value, density value)) Prod.fst measure)
    (map_id measure)

theorem densitySimulation_on_graph {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (density : α → NNRat) (point : α) :
    (densitySimulation measure density).mass (point, density point) = measure.mass point := by
  apply mass_map_injective
  intro left right equal
  exact congrArg Prod.fst equal

theorem densitySimulation_off_graph {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (density : α → NNRat) (point : α) (reported : NNRat)
    (incorrect : reported ≠ density point) :
    (densitySimulation measure density).mass (point, reported) = 0 := by
  apply mass_map_no_preimage
  intro value equal
  have valueEqual : value = point := congrArg Prod.fst equal
  subst value
  have densityEqual : density point = reported := congrArg Prod.snd equal
  exact incorrect densityEqual.symm

theorem densitySimulation_correct {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (density : α → NNRat) :
    IsDensitySimulation measure density (densitySimulation measure density) :=
  ⟨densitySimulation_value_marginal measure density,
    densitySimulation_on_graph measure density,
    densitySimulation_off_graph measure density⟩

end FiniteMeasure

namespace FinitePMF

def densitySimulation {α : Type u} (pmf : FinitePMF α)
    (density : α → NNRat) : FinitePMF (α × NNRat) :=
  map (fun value => (value, density value)) pmf

def IsDensitySimulation {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (density : α → NNRat)
    (output : FinitePMF (α × NNRat)) : Prop :=
  marginal₁ output ≈ₚ pmf ∧
    (∀ point, output.prob (point, density point) = pmf.prob point) ∧
    ∀ point reported, reported ≠ density point → output.prob (point, reported) = 0

theorem densitySimulation_value_marginal {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (density : α → NNRat) :
    marginal₁ (densitySimulation pmf density) ≈ₚ pmf := by
  exact Equivalent.trans
    (map_comp (fun value => (value, density value)) Prod.fst pmf)
    (map_id pmf)

theorem densitySimulation_on_graph {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (density : α → NNRat) (point : α) :
    (densitySimulation pmf density).prob (point, density point) = pmf.prob point := by
  apply prob_map_injective
  intro left right equal
  exact congrArg Prod.fst equal

theorem densitySimulation_off_graph {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (density : α → NNRat) (point : α) (reported : NNRat)
    (incorrect : reported ≠ density point) :
    (densitySimulation pmf density).prob (point, reported) = 0 := by
  apply FiniteMeasure.mass_map_no_preimage
  intro value equal
  have valueEqual : value = point := congrArg Prod.fst equal
  subst value
  have densityEqual : density point = reported := congrArg Prod.snd equal
  exact incorrect densityEqual.symm

theorem densitySimulation_correct {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (density : α → NNRat) :
    IsDensitySimulation pmf density (densitySimulation pmf density) :=
  ⟨densitySimulation_value_marginal pmf density,
    densitySimulation_on_graph pmf density,
    densitySimulation_off_graph pmf density⟩

end FinitePMF

end Foundations.Probability
