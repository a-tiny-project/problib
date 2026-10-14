module

public import Problib.Analysis.Real.Limit
public import Problib.Analysis.Real.Dominated
public import Problib.Analysis.Real.Sequence
public import Problib.Measure.Integral.Lebesgue.Markov
public import Problib.Measure.Integral.Real

/-! Convergence in probability.

A sequence of random readings converges in probability to a limit when, for
every tolerance, the mass of the draws that read farther than the tolerance
from the limit falls below every positive bound from some stage on. Each stage
carries its own law on its own space, so a reading at stage `count` may depend
on `count` draws.

Two closures make the notion usable. A function jointly continuous at the pair
of limits carries two convergent readings to the function of their limits,
which is how a ratio of convergent means converges. A reading whose mean
squared error vanishes converges in probability, by Markov's inequality applied
to the squared deviation. `meanSquare` states that error as a lower integral,
and `meanSquare_split` splits it into the variance about the mean and the
squared bias of the mean.
-/

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real
open Problib.Analysis.Real

universe u

noncomputable section

/-- The draws whose reading lies at least `tolerance` from `limit`. -/
@[expose] public def farEvent {α : Type u} (reading : α → Carrier)
    (limit tolerance : Carrier) : Set α :=
  fun x => le tolerance (abs (sub (reading x) limit))

/-- Readings converge in probability to `limit` under the stage laws when the
mass of every far event eventually falls below every positive bound. -/
@[expose] public def ConvergesInProbability {carriers : Nat → Type u}
    {spaces : (count : Nat) → Space (carriers count)}
    (laws : (count : Nat) → Measure (spaces count))
    (readings : (count : Nat) → carriers count → Carrier) (limit : Carrier) : Prop :=
  ∀ tolerance : Carrier, lt zero tolerance →
    ∀ mass : Carrier, lt zero mass →
      ∃ stage : Nat, ∀ count : Nat, stage ≤ count →
        ENNReal.le (laws count (farEvent (readings count) limit tolerance))
          (ENNReal.ofReal mass)

/-- A function jointly continuous at the pair of limits carries two readings
that converge in probability under the same laws to its value at the limits.
Continuity turns the tolerance into a radius, the far event of the image lies
inside the union of the two far events at that radius, and each of those has
at most half the mass bound. -/
public theorem convergesInProbability_map₂ {carriers : Nat → Type u}
    {spaces : (count : Nat) → Space (carriers count)}
    {laws : (count : Nat) → Measure (spaces count)}
    {first second : (count : Nat) → carriers count → Carrier}
    {firstLimit secondLimit : Carrier} {function : Carrier → Carrier → Carrier}
    (continuous : JointlyContinuousAt function firstLimit secondLimit)
    (firstConverges : ConvergesInProbability laws first firstLimit)
    (secondConverges : ConvergesInProbability laws second secondLimit) :
    ConvergesInProbability laws
      (fun count x => function (first count x) (second count x))
      (function firstLimit secondLimit) := by
  intro tolerance positive mass massPositive
  obtain ⟨radius, radiusPositive, close⟩ := continuous tolerance positive
  have halfPositive := half_positive massPositive
  obtain ⟨firstStage, firstBound⟩ :=
    firstConverges radius radiusPositive (half mass) halfPositive
  obtain ⟨secondStage, secondBound⟩ :=
    secondConverges radius radiusPositive (half mass) halfPositive
  refine ⟨max firstStage secondStage, fun count later => ?_⟩
  have covered : Set.Subset
      (farEvent (fun x => function (first count x) (second count x))
        (function firstLimit secondLimit) tolerance)
      (Set.union (farEvent (first count) firstLimit radius)
        (farEvent (second count) secondLimit radius)) := by
    intro x far
    classical
    by_cases firstFar : le radius (abs (sub (first count x) firstLimit))
    · exact Or.inl firstFar
    by_cases secondFar : le radius (abs (sub (second count x) secondLimit))
    · exact Or.inr secondFar
    exact absurd far (not_le_of_lt
      (close (first count x) (second count x)
        (lt_of_not_le firstFar) (lt_of_not_le secondFar)))
  have firstMass := firstBound count (Nat.le_trans (Nat.le_max_left _ _) later)
  have secondMass := secondBound count (Nat.le_trans (Nat.le_max_right _ _) later)
  refine ENNReal.le_trans (Measure.mono (laws count) covered)
    (ENNReal.le_trans (Measure.union_le (laws count) _ _) ?_)
  rw [← add_half mass, ENNReal.ofReal_add halfPositive.1 halfPositive.1]
  exact ENNReal.add_le_add firstMass secondMass

/-- A ratio of readings converges in probability to the ratio of their limits
when the denominator's limit is nonzero. -/
public theorem convergesInProbability_div {carriers : Nat → Type u}
    {spaces : (count : Nat) → Space (carriers count)}
    {laws : (count : Nat) → Measure (spaces count)}
    {numerator denominator : (count : Nat) → carriers count → Carrier}
    {numeratorLimit denominatorLimit : Carrier}
    (denominatorNonzero : denominatorLimit ≠ zero)
    (numeratorConverges : ConvergesInProbability laws numerator numeratorLimit)
    (denominatorConverges : ConvergesInProbability laws denominator denominatorLimit) :
    ConvergesInProbability laws
      (fun count x => div (numerator count x) (denominator count x))
      (div numeratorLimit denominatorLimit) :=
  convergesInProbability_map₂ (jointlyContinuousAt_div denominatorNonzero)
    numeratorConverges denominatorConverges

/-- The product of two nonnegative reals read as extended nonnegative values. -/
private theorem ofReal_mul {left right : Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    ENNReal.ofReal (mul left right) =
      ENNReal.mul (ENNReal.ofReal left) (ENNReal.ofReal right) := by
  unfold ENNReal.ofReal
  rw [ENNReal.finite_mul_finite]
  congr 1
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal leftNonnegative,
    NNReal.toReal_ofReal rightNonnegative,
    NNReal.toReal_ofReal (mul_nonnegative leftNonnegative rightNonnegative)]

/-- A tolerance below a deviation's size bounds its square below the squared
deviation. -/
private theorem square_le_of_le_abs {tolerance deviation : Carrier}
    (nonnegative : le zero tolerance) (far : le tolerance (abs deviation)) :
    le (mul tolerance tolerance) (mul deviation deviation) := by
  have squared : mul (abs deviation) (abs deviation) = mul deviation deviation := by
    rw [← abs_mul, abs_of_nonnegative (mul_self_nonnegative deviation)]
  rw [← squared]
  exact le_trans (mul_le_mul_nonnegative_left far nonnegative)
    (mul_le_mul_nonnegative_right far (abs_nonnegative deviation))

/-- Readings whose mean squared error about `limit` vanishes converge in
probability to it. Markov's inequality at the squared tolerance bounds the far
mass by the mean squared error over the squared tolerance, and the error
eventually falls below the squared tolerance times any mass bound. -/
public theorem convergesInProbability_of_meanSquare {carriers : Nat → Type u}
    {spaces : (count : Nat) → Space (carriers count)}
    {laws : (count : Nat) → Measure (spaces count)}
    {readings : (count : Nat) → carriers count → Carrier} {limit : Carrier}
    {errors : Nat → Carrier}
    (integral : ∀ count, HasRealIntegral (laws count)
      (fun x => mul (sub (readings count x) limit) (sub (readings count x) limit))
      (errors count))
    (vanishing : ConvergesTo errors zero) :
    ConvergesInProbability laws readings limit := by
  intro tolerance positive mass massPositive
  have squarePositive := mul_positive positive positive
  obtain ⟨stage, small⟩ := vanishing (mul (mul tolerance tolerance) mass)
    (mul_positive squarePositive massPositive)
  refine ⟨stage, fun count later => ?_⟩
  have errorBound : le (errors count) (mul (mul tolerance tolerance) mass) := by
    have below := (small count later).1
    rw [sub_zero] at below
    exact le_trans (le_abs _) below
  have nonnegative : ∀ x, le zero
      (mul (sub (readings count x) limit) (sub (readings count x) limit)) :=
    fun x => mul_self_nonnegative _
  obtain ⟨parts, same⟩ := integral count
  have measurable : ENNRealMeasurable (spaces count) (fun x => ENNReal.ofReal
      (mul (sub (readings count x) limit) (sub (readings count x) limit))) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable parts.measurable
  have covered : Set.Subset (farEvent (readings count) limit tolerance)
      (upperLevel (fun x => ENNReal.ofReal
        (mul (sub (readings count x) limit) (sub (readings count x) limit)))
        (ENNReal.ofReal (mul tolerance tolerance))) := by
    intro x far
    exact ENNReal.ofReal_monotone (square_le_of_le_abs positive.1 far)
  have markovBound := Measure.markov (laws count) measurable
    (ENNReal.ofReal (mul tolerance tolerance))
  rw [HasRealIntegral.lintegral_ofReal nonnegative ⟨parts, same⟩] at markovBound
  have scaled : ENNReal.le
      (ENNReal.mul (ENNReal.ofReal (mul tolerance tolerance))
        (laws count (farEvent (readings count) limit tolerance)))
      (ENNReal.mul (ENNReal.ofReal (mul tolerance tolerance)) (ENNReal.ofReal mass)) := by
    rw [← ofReal_mul squarePositive.1 massPositive.1]
    exact ENNReal.le_trans
      (ENNReal.le_trans
        (ENNReal.mul_le_mul_left (Measure.mono (laws count) covered) _) markovBound)
      (ENNReal.ofReal_monotone errorBound)
  have thresholdPositive : ENNReal.lt ENNReal.zero
      (ENNReal.ofReal (mul tolerance tolerance)) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) squarePositive.1).mpr squarePositive
  exact (ENNReal.mul_le_mul_left_iff (ENNReal.ofReal_finite _) thresholdPositive).mp scaled

/-! ### Mean squares -/

/-- The mean square distance `∫ (reading − value)² dμ` of a reading from a
value. -/
@[expose] public def meanSquare {α : Type u} {space : Space α} (measure : Measure space)
    (reading : α → Carrier) (value : Carrier) : ENNReal :=
  lintegral measure fun x => ENNReal.ofReal
    (mul (sub (reading x) value) (sub (reading x) value))

section MeanSquare

variable {α : Type u} {space : Space α} {measure : Measure space}

/-- The squared deviation of a measurable reading is measurable. -/
public theorem meanSquare_integrand_measurable {reading : α → Carrier}
    (measurable : MeasurableMap space borel reading) (value : Carrier) :
    ENNRealMeasurable space fun x => ENNReal.ofReal
      (mul (sub (reading x) value) (sub (reading x) value)) := by
  have centred : MeasurableMap space borel fun x => sub (reading x) value :=
    measurable_sub measurable (MeasurableMap.constant space borel value)
  exact ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
    (measurable_mul centred centred)

/-- A certified mean square is the mean square. -/
public theorem meanSquare_eq {reading : α → Carrier} {value error : Carrier}
    (integral : HasRealIntegral measure (fun x =>
      mul (sub (reading x) value) (sub (reading x) value)) error) :
    meanSquare measure reading value = ENNReal.ofReal error :=
  integral.lintegral_ofReal fun _ => mul_self_nonnegative _

/-- A measurable centered square with a finite mean square has a certified one. -/
public theorem hasRealIntegral_of_meanSquare {reading : α → Carrier} {value : Carrier}
    (measurable : MeasurableMap space borel fun x =>
      mul (sub (reading x) value) (sub (reading x) value))
    (finite : ENNReal.Finite (meanSquare measure reading value)) :
    HasRealIntegral measure (fun x =>
      mul (sub (reading x) value) (sub (reading x) value))
      (ENNReal.toReal (meanSquare measure reading value)) := by
  have vanishes : (fun x => ENNReal.ofReal (neg
      (mul (sub (reading x) value) (sub (reading x) value)))) =
      fun _ => ENNReal.zero := funext fun x =>
    ENNReal.ofReal_eq_zero_iff.mpr
      (neg_nonpositive_iff.mp (mul_self_nonnegative _))
  have negativeFinite : ENNReal.Finite (lintegral measure fun x => ENNReal.ofReal (neg
      (mul (sub (reading x) value) (sub (reading x) value)))) := by
    rw [vanishes, lintegral_zero]
    exact True.intro
  let canonical := IntegralParts.canonical measurable finite negativeFinite
  refine ⟨canonical, ?_⟩
  have certified := HasRealIntegral.lintegral_ofReal (fun _ => mul_self_nonnegative _)
    ⟨canonical, rfl⟩
  have nonnegative := HasRealIntegral.value_nonnegative (fun _ => mul_self_nonnegative _)
    ⟨canonical, rfl⟩
  change meanSquare measure reading value = _ at certified
  rw [certified, ENNReal.toReal_ofReal nonnegative]

/-- The mean square about a value is the variance about the mean plus the
square of the mean's distance from the value. -/
public theorem meanSquare_split (probability : Measure.IsProbability measure)
    {reading : α → Carrier} {mean spread : Carrier}
    (meanIntegral : HasRealIntegral measure reading mean)
    (spreadIntegral : HasRealIntegral measure (fun x =>
      mul (sub (reading x) mean) (sub (reading x) mean)) spread)
    (value : Carrier) :
    meanSquare measure reading value =
      ENNReal.add (ENNReal.ofReal spread)
        (ENNReal.ofReal (mul (sub mean value) (sub mean value))) := by
  have centred : HasRealIntegral measure (fun x => sub (reading x) mean)
      zero := by
    have difference := meanIntegral.sub (HasRealIntegral.const probability mean)
    rwa [sub_self] at difference
  have cross := centred.smul (sub mean value)
  have summed := (spreadIntegral.add cross).add
    (cross.add (HasRealIntegral.const probability
      (mul (sub mean value) (sub mean value))))
  rw [mul_zero, add_zero, zero_add] at summed
  have expanded : HasRealIntegral measure (fun x =>
      mul (sub (reading x) value) (sub (reading x) value))
      (add spread
        (mul (sub mean value) (sub mean value))) := by
    refine summed.congr fun x => ?_
    rw [← sub_add_sub (reading x) mean value, add_mul, mul_add,
      mul_add, mul_comm (sub (reading x) mean)
        (sub mean value)]
  rw [meanSquare_eq expanded, ENNReal.ofReal_add
    (HasRealIntegral.value_nonnegative (fun _ => mul_self_nonnegative _) spreadIntegral)
    (mul_self_nonnegative _)]

end MeanSquare

end

end Problib.Measure
