module

public import Problib.Analysis.Real.Sequence
public import Problib.Measure.Integral.Real
public import Problib.Measure.Integral.Lebesgue.Dominated

/-! Dominated convergence for the certified finite signed integral.

`HasRealIntegral` certifies a value by any finite measurable decomposition, so
a limit theorem cannot read the parts it is handed. It reads the integral of
the absolute value instead. `abs_value_le` bounds a certified value by that
integral through uniqueness against the canonical decomposition, and dominated
convergence is then the lower-integral theorem of
`Problib.Measure.Integral.Lebesgue.Dominated` applied to the absolute
differences, which converge to zero pointwise.

Two forms are proved. `dominated_convergence` takes a `Nat`-indexed sequence.
`dominated_convergence_approaches` takes a family indexed by a nonzero
displacement and concludes a punctured limit, which is the form a difference
quotient needs. The limit integrand's measurability is a hypothesis in both.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real

universe u

variable {α : Type u} {space : Space α}

noncomputable section

/-! ### Pointwise facts about sizes -/

/-- A nonnegative real, read on the signed carrier, is nonnegative. -/
private theorem toReal_nonnegative (value : NNReal) : le zero value.toReal :=
  value.property

/-- The size of a real, embedded, is the sum of its embedded parts. -/
public theorem ofReal_abs (value : selection.Carrier) :
    ENNReal.ofReal (abs value) =
      ENNReal.add (ENNReal.ofReal value) (ENNReal.ofReal (neg value)) := by
  rcases le_total zero value with nonnegative | nonpositive
  · have vanishes : ENNReal.ofReal (neg value) = ENNReal.zero :=
      ENNReal.ofReal_eq_zero_iff.mpr (neg_nonpositive_iff.mp nonnegative)
    rw [abs_of_nonnegative nonnegative, vanishes, ENNReal.add_zero]
  · have vanishes : ENNReal.ofReal value = ENNReal.zero :=
      ENNReal.ofReal_eq_zero_iff.mpr nonpositive
    rw [abs_of_nonpositive nonpositive, vanishes, ENNReal.zero_add]

/-- A difference of nonnegatives is no larger in size than their sum. -/
public theorem abs_sub_le_add {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le (abs (sub left right)) (add left right) := by
  have negRight : le (neg right) right :=
    le_trans (neg_nonpositive_iff.mp rightNonnegative) rightNonnegative
  have negLeft : le (neg left) left :=
    le_trans (neg_nonpositive_iff.mp leftNonnegative) leftNonnegative
  apply abs_le.mpr
  constructor
  · rw [neg_add, sub_eq_add_neg]
    exact add_le_add_right_iff.mpr negLeft
  · rw [sub_eq_add_neg]
    exact add_le_add_left_iff.mpr negRight

/-- The embedded size of a real integrand is measurable when the integrand is. -/
public theorem abs_measurable {integrand : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand) :
    ENNRealMeasurable space (fun x => ENNReal.ofReal (abs (integrand x))) := by
  have positive : ENNRealMeasurable space (fun x => ENNReal.ofReal (integrand x)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable measurable
  have negative : ENNRealMeasurable space (fun x => ENNReal.ofReal (neg (integrand x))) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (by
        intro set measurableSet
        exact MeasurableMap.comp neg_measurable measurable measurableSet)
  have same : (fun x => ENNReal.ofReal (abs (integrand x))) =
      fun x => ENNReal.add (ENNReal.ofReal (integrand x))
        (ENNReal.ofReal (neg (integrand x))) :=
    funext fun x => ofReal_abs (integrand x)
  rw [same]
  exact positive.add negative

/-! ### Sizes of certified integrals -/

/-- A certified integrand has an integrable size: it is bounded by the sum of
its two parts, whose integrals are finite. -/
public theorem _root_.Problib.Measure.IntegralParts.lintegral_abs_finite {measure : Measure space}
    {integrand : α → selection.Carrier} (parts : IntegralParts measure integrand) :
    ENNReal.Finite (lintegral measure (fun x => ENNReal.ofReal (abs (integrand x)))) := by
  have pointwise : ∀ x, ENNReal.le (ENNReal.ofReal (abs (integrand x)))
      (ENNReal.add (ENNReal.finite (parts.positive x))
        (ENNReal.finite (parts.negative x))) := by
    intro x
    have bound : le (abs (integrand x))
        (add (parts.positive x).toReal (parts.negative x).toReal) := by
      rw [parts.decomposition x]
      exact abs_sub_le_add (toReal_nonnegative (parts.positive x))
        (toReal_nonnegative (parts.negative x))
    have embedded := ENNReal.ofReal_monotone bound
    rw [ENNReal.ofReal_add (toReal_nonnegative (parts.positive x))
      (toReal_nonnegative (parts.negative x))] at embedded
    have positiveBack : ENNReal.ofReal (parts.positive x).toReal =
        ENNReal.finite (parts.positive x) :=
      ENNReal.ofReal_toReal_finite (parts.positive x)
    have negativeBack : ENNReal.ofReal (parts.negative x).toReal =
        ENNReal.finite (parts.negative x) :=
      ENNReal.ofReal_toReal_finite (parts.negative x)
    rwa [positiveBack, negativeBack] at embedded
  have summed := lintegral_mono measure pointwise
  rw [lintegral_add measure parts.positive_measurable parts.negative_measurable,
    parts.positive_integral, parts.negative_integral] at summed
  exact ENNReal.finite_of_le summed
    (ENNReal.add_finite (ENNReal.finite_ne_top _ |> ENNReal.finite_iff_ne_top.mpr)
      (ENNReal.finite_ne_top _ |> ENNReal.finite_iff_ne_top.mpr))

/-- A measurable integrand with an integrable size is certified by its
canonical positive and negative parts. -/
@[expose] public noncomputable def _root_.Problib.Measure.IntegralParts.ofSizeFinite {measure : Measure space}
    {integrand : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand)
    (sizeFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (abs (integrand x))))) :
    IntegralParts measure integrand :=
  IntegralParts.canonical measurable
    (ENNReal.finite_of_le
      (lintegral_mono measure (fun x => ENNReal.ofReal_monotone (le_abs (integrand x))))
      sizeFinite)
    (ENNReal.finite_of_le
      (lintegral_mono measure (fun x => ENNReal.ofReal_monotone (by
        have flipped := le_abs (neg (integrand x))
        rwa [abs_neg] at flipped)))
      sizeFinite)

/-- A measurable integrand whose size is below a certified one is certified. -/
@[expose] public noncomputable def _root_.Problib.Measure.IntegralParts.ofDominated {measure : Measure space}
    {integrand dominator : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand)
    (bounded : ∀ x, le (abs (integrand x)) (dominator x))
    (dominatorParts : IntegralParts measure dominator) :
    IntegralParts measure integrand :=
  IntegralParts.ofSizeFinite measurable
    (ENNReal.finite_of_le
      (lintegral_mono measure (fun x =>
        ENNReal.ofReal_monotone (le_trans (bounded x) (le_abs (dominator x)))))
      dominatorParts.lintegral_abs_finite)

/-- A certified value is no larger in size than the integral of the size of
its integrand. Uniqueness moves the value onto the canonical decomposition,
where the bound is the pointwise sum of the two parts. -/
public theorem _root_.Problib.Measure.IntegralParts.abs_value_le {measure : Measure space}
    {integrand : α → selection.Carrier} (parts : IntegralParts measure integrand) :
    ENNReal.le (ENNReal.ofReal (abs parts.value))
      (lintegral measure (fun x => ENNReal.ofReal (abs (integrand x)))) := by
  let canonical := IntegralParts.ofSizeFinite parts.measurable parts.lintegral_abs_finite
  have integralSum : lintegral measure (fun x => ENNReal.ofReal (abs (integrand x))) =
      ENNReal.add (ENNReal.finite canonical.positiveMass)
        (ENNReal.finite canonical.negativeMass) := by
    rw [← canonical.positive_integral, ← canonical.negative_integral,
      ← lintegral_add measure canonical.positive_measurable canonical.negative_measurable]
    exact congrArg (lintegral measure) (funext fun x => ofReal_abs (integrand x))
  have bound := ENNReal.ofReal_monotone
    (abs_sub_le_add (toReal_nonnegative canonical.positiveMass)
      (toReal_nonnegative canonical.negativeMass))
  rw [ENNReal.ofReal_add (toReal_nonnegative canonical.positiveMass)
    (toReal_nonnegative canonical.negativeMass)] at bound
  have positiveBack : ENNReal.ofReal canonical.positiveMass.toReal =
      ENNReal.finite canonical.positiveMass :=
    ENNReal.ofReal_toReal_finite _
  have negativeBack : ENNReal.ofReal canonical.negativeMass.toReal =
      ENNReal.finite canonical.negativeMass :=
    ENNReal.ofReal_toReal_finite _
  rw [positiveBack, negativeBack] at bound
  rw [parts.unique canonical, integralSum]
  exact bound

/-! ### Real convergence read through the extended scale -/

/-- A strictly positive extended value lies above the embedding of some
positive real. -/
private theorem positive_real_below {error : ENNReal} (positive : ENNReal.lt ENNReal.zero error) :
    ∃ epsilon : selection.Carrier, lt zero epsilon ∧
      ENNReal.le (ENNReal.ofReal epsilon) error := by
  cases error with
  | top => exact ⟨one, one_positive, ENNReal.le_top _⟩
  | finite value =>
      have back : ENNReal.ofReal value.toReal = ENNReal.finite value :=
        ENNReal.ofReal_toReal_finite value
      refine ⟨value.toReal, ?_, by
        rw [back]
        exact ENNReal.le_refl _⟩
      have embedded := (ENNReal.toReal_lt_toReal_iff (ENNReal.finite_ne_top _ |>
        ENNReal.finite_iff_ne_top.mpr) (ENNReal.finite_ne_top _ |>
        ENNReal.finite_iff_ne_top.mpr)).mpr positive
      exact embedded

/-- Sizes that converge to zero in the real sense have both extended limits
at zero. -/
private theorem size_limits_vanish {values : Nat → selection.Carrier}
    (converges : ConvergesTo values zero) :
    ENNReal.liminf (fun index => ENNReal.ofReal (abs (values index))) = ENNReal.zero ∧
      ENNReal.limsup (fun index => ENNReal.ofReal (abs (values index))) = ENNReal.zero := by
  have upper : ENNReal.limsup (fun index => ENNReal.ofReal (abs (values index))) =
      ENNReal.zero := by
    apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
    apply ENNReal.le_of_forall_positive_le_add
    intro error errorPositive
    rw [ENNReal.zero_add]
    rcases positive_real_below errorPositive with ⟨epsilon, epsilonPositive, below⟩
    rcases converges epsilon epsilonPositive with ⟨stage, close⟩
    refine ENNReal.le_trans (ENNReal.limsup_le_of_eventually ⟨stage, fun offset => ?_⟩) below
    have near := close (stage + offset) (Nat.le_add_right stage offset)
    rw [sub_zero] at near
    exact ENNReal.ofReal_monotone (le_of_lt near)
  refine ⟨?_, upper⟩
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  rw [← upper]
  exact ENNReal.liminf_le_limsup _

/-! ### Dominated convergence -/

/-- Dominated convergence for the certified integral along a sequence. A
pointwise convergent sequence of certified integrands, dominated by one
certified function, has a certified measurable limit whose integral is the
limit of the integrals. -/
public theorem dominated_convergence {measure : Measure space}
    {functions : Nat → α → selection.Carrier} {values : Nat → selection.Carrier}
    {limit dominator : α → selection.Carrier} {dominatorValue : selection.Carrier}
    (integrals : ∀ index, HasRealIntegral measure (functions index) (values index))
    (limitMeasurable : MeasurableMap space borel limit)
    (dominatorIntegral : HasRealIntegral measure dominator dominatorValue)
    (dominated : ∀ index point, le (abs (functions index point)) (dominator point))
    (pointwise : ∀ point,
      ConvergesTo (fun index => functions index point) (limit point)) :
    ∃ value, HasRealIntegral measure limit value ∧ ConvergesTo values value := by
  classical
  obtain ⟨dominatorParts, _⟩ := dominatorIntegral
  have limitBound : ∀ point, le (abs (limit point)) (dominator point) :=
    fun point => abs_le_of_convergesTo (pointwise point) (fun index => dominated index point)
  let limitParts := IntegralParts.ofDominated limitMeasurable limitBound dominatorParts
  refine ⟨limitParts.value, ⟨limitParts, rfl⟩, ?_⟩
  let chosen := fun index => Classical.choose (integrals index)
  have chosenValue : ∀ index, (chosen index).value = values index :=
    fun index => Classical.choose_spec (integrals index)
  let difference := fun index =>
    ((chosen index).addParts limitParts.negParts).congr
      (fun point => (sub_eq_add_neg (functions index point) (limit point)).symm)
  have differenceValue : ∀ index,
      (difference index).value = sub (values index) limitParts.value := by
    intro index
    show ((chosen index).addParts limitParts.negParts).value = _
    rw [IntegralParts.addParts_value, IntegralParts.negParts_value, chosenValue,
      ← sub_eq_add_neg]
  let sizes := fun index point =>
    ENNReal.ofReal (abs (sub (functions index point) (limit point)))
  have sizesMeasurable : ∀ index, ENNRealMeasurable space (sizes index) :=
    fun index => abs_measurable (difference index).measurable
  let envelope := fun point => ENNReal.add (ENNReal.ofReal (abs (dominator point)))
    (ENNReal.ofReal (abs (limit point)))
  have sizesDominated : ∀ index point, ENNReal.le (sizes index point) (envelope point) := by
    intro index point
    have triangle := abs_add_le (functions index point) (neg (limit point))
    rw [abs_neg, ← sub_eq_add_neg] at triangle
    have widened := le_trans triangle (add_le_add_right_iff.mpr
      (le_trans (dominated index point) (le_abs (dominator point))))
    have embedded := ENNReal.ofReal_monotone widened
    rwa [ENNReal.ofReal_add (abs_nonnegative _) (abs_nonnegative _)] at embedded
  have envelopeFinite : ENNReal.Finite (lintegral measure envelope) := by
    rw [lintegral_add measure (abs_measurable dominatorParts.measurable)
      (abs_measurable limitMeasurable)]
    exact ENNReal.add_finite dominatorParts.lintegral_abs_finite
      limitParts.lintegral_abs_finite
  have vanishing := fun point => size_limits_vanish (values := fun index =>
    sub (functions index point) (limit point)) (by
      intro epsilon positive
      rcases pointwise point epsilon positive with ⟨stage, close⟩
      exact ⟨stage, fun index later => by rw [sub_zero]; exact close index later⟩)
  have converged := lintegral_dominated_convergence measure sizes (fun _ => ENNReal.zero)
    envelope sizesMeasurable sizesDominated envelopeFinite
    (fun point => (vanishing point).left) (fun point => (vanishing point).right)
  rw [lintegral_zero] at converged
  intro epsilon positive
  have epsilonEmbedded : ENNReal.lt ENNReal.zero (ENNReal.ofReal epsilon) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (le_of_lt positive)).mpr positive
  rw [← converged.right] at epsilonEmbedded
  rcases ENNReal.eventually_lt_of_limsup_lt epsilonEmbedded with ⟨stage, small⟩
  refine ⟨stage, fun index later => ?_⟩
  have shifted : index = stage + (index - stage) := (Nat.add_sub_cancel' later).symm
  have integralSmall := small (index - stage)
  rw [← shifted] at integralSmall
  have valueBound := (difference index).abs_value_le
  rw [differenceValue] at valueBound
  have combined : ENNReal.lt (ENNReal.ofReal (abs (sub (values index) limitParts.value)))
      (ENNReal.ofReal epsilon) :=
    ⟨ENNReal.le_trans valueBound integralSmall.left,
      fun back => integralSmall.right (ENNReal.le_trans back valueBound)⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (abs_nonnegative _) (le_of_lt positive)).mp combined

/-- Dominated convergence for the certified integral along a punctured limit.
A family of certified integrands indexed by a nonzero displacement inside a
radius, dominated there by one certified function and converging pointwise to
a measurable limit, has a certified limit whose integral is the punctured
limit of the integrals. -/
public theorem dominated_convergence_approaches {measure : Measure space}
    {family : selection.Carrier → α → selection.Carrier}
    {values : selection.Carrier → selection.Carrier}
    {limit dominator : α → selection.Carrier}
    {radius dominatorValue : selection.Carrier} (radiusPositive : lt zero radius)
    (integrals : ∀ displacement, displacement ≠ zero → lt (abs displacement) radius →
      HasRealIntegral measure (family displacement) (values displacement))
    (limitMeasurable : MeasurableMap space borel limit)
    (dominatorIntegral : HasRealIntegral measure dominator dominatorValue)
    (dominated : ∀ displacement, displacement ≠ zero → lt (abs displacement) radius →
      ∀ point, le (abs (family displacement point)) (dominator point))
    (pointwise : ∀ point,
      Approaches (fun displacement => family displacement point) (limit point)) :
    ∃ value, HasRealIntegral measure limit value ∧ Approaches values value := by
  have alongSequence : ∀ displacements : Nat → selection.Carrier,
      (∀ index, displacements index ≠ zero) →
        (∀ index, lt (abs (displacements index)) radius) →
          ConvergesTo displacements zero →
            ∃ value, HasRealIntegral measure limit value ∧
              ConvergesTo (fun index => values (displacements index)) value :=
    fun displacements nonzero inside null =>
      dominated_convergence
        (fun index => integrals (displacements index) (nonzero index) (inside index))
        limitMeasurable dominatorIntegral
        (fun index => dominated (displacements index) (nonzero index) (inside index))
        (fun point => convergesTo_of_approaches (pointwise point) nonzero null)
  rcases exists_null_sequence radiusPositive with ⟨witness, nonzero, inside, null⟩
  rcases alongSequence witness nonzero inside null with ⟨value, integral, _⟩
  refine ⟨value, integral, approaches_of_sequences radiusPositive ?_⟩
  intro displacements nonzero inside null
  rcases alongSequence displacements nonzero inside null with
    ⟨other, otherIntegral, converges⟩
  rwa [HasRealIntegral.unique integral otherIntegral]

end

end Problib.Analysis.Real
