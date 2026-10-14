module

public import Problib.Analysis.Trigonometric.Rotation
public import Problib.Analysis.Trigonometric.Measurable
public import Problib.Analysis.Trigonometric.Pi
public import Problib.Analysis.Arctangent.Inverse
public import Problib.Measure.Uniform
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
import Problib.Real.Grind

/-! The uniform law on the unit circle, and the only rotation-invariant one.

A turn `t` names the point `(cos 2πt, sin 2πt)` of the unit circle. The circle
law is the law of a turn drawn uniformly from `[0, 1]`. This file proves that it
is the only probability law on the plane that lives on the unit circle and is
kept by every rotation (`eq_circleLaw_of_rotation_invariant`).

The proof averages over rotations. Fix such a law `Q` and a measurable event
`A`. Rotating by a uniform turn changes nothing, so `Q(A)` is the average over
`u` of `Q(R_u⁻¹ A)`. Tonelli exchanges the two integrals, which gives the
average over `p ~ Q` of `P(R_U p ∈ A)`. Every point of the circle is a turn `c`
(`turn_surjective`, through the arctangent), and rotating it by the turn `u`
gives the turn `c + u`. A uniform turn shifted by `c` is still uniform on the
circle (`circleLaw_shift`), because Lebesgue volume is translation invariant
and the turn has period one. So the inner probability is `circleLaw(A)` at
every `p` on the circle, and `Q(A) = circleLaw(A)`.

The proof computes no angle. It needs no `atan2`, no inverse of the turn, and
no sector area.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-! ### Turns -/

/-- The point of the unit circle at `t` turns: `(cos 2πt, sin 2πt)`. -/
@[expose] public def turn (turns : Carrier) : Carrier × Carrier :=
  (cos (mul (mul two pi) turns), sin (mul (mul two pi) turns))

private theorem angle_measurable :
    MeasurableMap borel borel (fun turns : Carrier => mul (mul two pi) turns) :=
  measurable_mul (MeasurableMap.constant _ borel _) (MeasurableMap.identity borel)

public theorem turn_measurable : MeasurableMap borel (Space.product borel borel) turn :=
  Space.pair_measurable (MeasurableMap.comp cos_measurable angle_measurable)
    (MeasurableMap.comp sin_measurable angle_measurable)

/-- Every turn lies on the unit circle. -/
public theorem squaredNorm_turn (turns : Carrier) : squaredNorm (turn turns) = one := by
  have pythagoras := sin_sq_add_cos_sq (mul (mul two pi) turns)
  unfold squaredNorm turn
  real_grind

/-- A turn has period one. -/
public theorem turn_add_one (turns : Carrier) : turn (add turns one) = turn turns := by
  unfold turn
  rw [cos_turn_add_one, sin_turn_add_one]

/-- Rotating the turn `u` by the turn `c` gives the turn `c + u`. -/
public theorem rotation_turn (first second : Carrier) :
    rotation (turn first).1 (turn first).2 (turn second) = turn (add first second) := by
  have split : mul (mul two pi) (add first second) =
      add (mul (mul two pi) first) (mul (mul two pi) second) := by real_grind
  unfold rotation turn
  rw [split, cos_add, sin_add]

/-! ### Every point of the circle is a turn -/

/-- Two positive reals with equal squares are equal. -/
private theorem eq_of_square_eq {left right : Carrier} (leftPositive : lt zero left)
    (rightPositive : lt zero right) (square : mul left left = mul right right) : left = right := by
  have factored : mul (sub left right) (add left right) = zero := by real_grind
  rcases mul_eq_zero_iff.mp factored with same | opposite
  · real_grind
  · exfalso
    real_grind

/-- A point of the unit circle is the cosine and sine of an angle within one
full turn of zero. -/
private theorem exists_angle {first second : Carrier} (unit : squaredNorm (first, second) = one) :
    ∃ angle, lt (neg (mul two pi)) angle ∧ lt angle (mul two pi) ∧
      cos angle = first ∧ sin angle = second := by
  unfold squaredNorm at unit
  have piPositive := pi_positive
  have lowerBound := neg_half_pi_lt_atan (div second first)
  have upperBound := atan_lt_half_pi (div second first)
  have square := cos_atan_sq (div second first)
  have cosinePositive := cos_atan_positive (div second first)
  have sine := sin_atan (div second first)
  unfold half two at lowerBound upperBound
  unfold two
  by_cases positive : lt zero first
  · have nonzero := nonzero_of_positive positive
    have cosine : cos (atan (div second first)) = first := by
      apply eq_of_square_eq cosinePositive positive
      generalize cos (atan (div second first)) = c at *
      real_grind
    refine ⟨atan (div second first), by real_grind, by real_grind, cosine, ?_⟩
    rw [sine, cosine]
    real_grind
  · by_cases negative : lt first zero
    · have nonzero : first ≠ zero := fun equal => lt_irrefl zero (equal ▸ negative)
      have opposite : lt zero (neg first) := by real_grind
      have cosine : cos (atan (div second first)) = neg first := by
        apply eq_of_square_eq cosinePositive opposite
        generalize cos (atan (div second first)) = c at *
        real_grind
      refine ⟨add (atan (div second first)) pi, by real_grind, by real_grind, ?_, ?_⟩
      · rw [cos_add, cos_pi, sin_pi, cosine]
        real_grind
      · rw [sin_add, cos_pi, sin_pi, sine, cosine]
        real_grind
    · have vanishing : first = zero := by
        have above := not_lt_iff_le.mp positive
        have below := not_lt_iff_le.mp negative
        real_grind
      subst vanishing
      have factored : mul (sub second one) (add second one) = zero := by real_grind
      have quarterCosine := cos_half_pi
      have quarterSine := sin_half_pi
      unfold half two at quarterCosine quarterSine
      rcases mul_eq_zero_iff.mp factored with up | down
      · refine ⟨div pi (selection.ofRat 2), by real_grind, by real_grind, quarterCosine, ?_⟩
        rw [quarterSine]
        real_grind
      · refine ⟨neg (div pi (selection.ofRat 2)), by real_grind, by real_grind, ?_, ?_⟩
        · rw [cos_neg, quarterCosine]
        · rw [sin_neg, quarterSine]
          real_grind

/-- Every point of the unit circle is a turn in `[0, 1)`. -/
public theorem turn_surjective {point : Carrier × Carrier} (unit : squaredNorm point = one) :
    ∃ turns, le zero turns ∧ lt turns one ∧ turn turns = point := by
  obtain ⟨angle, lower, upper, cosine, sine⟩ := exists_angle unit
  have fullPositive : lt zero (mul two pi) := by
    have piPositive := pi_positive
    unfold two
    real_grind
  have nonzero := nonzero_of_positive fullPositive
  have scaled : mul (mul two pi) (div angle (mul two pi)) = angle := by
    generalize mul two pi = full at *
    real_grind
  have below : lt (div angle (mul two pi)) one := by
    apply (mul_lt_mul_left_iff fullPositive).mp
    rw [scaled]
    real_grind
  have above : lt (neg one) (div angle (mul two pi)) := by
    apply (mul_lt_mul_left_iff fullPositive).mp
    rw [scaled]
    real_grind
  have angleTurn : turn (div angle (mul two pi)) = point := by
    unfold turn
    rw [scaled, cosine, sine]
  by_cases nonnegative : le zero (div angle (mul two pi))
  · exact ⟨div angle (mul two pi), nonnegative, below, angleTurn⟩
  · have negative := not_le_iff_lt.mp nonnegative
    refine ⟨add (div angle (mul two pi)) one, by real_grind, by real_grind, ?_⟩
    rw [turn_add_one, angleTurn]

/-! ### The circle law -/

/-- The uniform law on the unit circle: a uniform turn in `[0, 1]`. -/
@[expose] public def circleLaw : Measure (Space.product borel borel) :=
  restrictedUnit.map turn turn_measurable

public theorem circleLaw_isProbability : Measure.IsProbability circleLaw :=
  restrictedUnit_isProbability.map turn turn_measurable

/-- The two closed and half-open unit intervals differ by a null point. -/
private theorem volume_inter_icc (region : Set Carrier) (lower upper : Carrier) :
    volume (Set.inter region (Icc lower upper)) = volume (Set.inter region (Ioc lower upper)) := by
  apply ENNReal.le_antisymm
  · have covered : Set.Subset (Set.inter region (Icc lower upper))
        (Set.union (Set.inter region (Ioc lower upper)) (Set.singleton lower)) := by
      intro value member
      by_cases strict : lt lower value
      · exact Or.inl ⟨member.1, strict, member.2.2⟩
      · have below := not_lt_iff_le.mp strict
        exact Or.inr (le_antisymm below member.2.1)
    have bound := ENNReal.le_trans (volume.mono covered) (volume.union_le _ _)
    rw [volume_singleton, ENNReal.add_zero] at bound
    exact bound
  · exact volume.mono (fun value member => ⟨member.1, member.2.1.1, member.2.2⟩)

/-- Translation keeps the volume of a measurable set. -/
private theorem volume_preimage_translate (shift : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    volume (Set.preimage (add shift) region) = volume region := by
  have translated := congrArg (fun measure : Measure borel => measure region)
    (map_volume_translate shift)
  rw [Measure.map_apply _ _ _ measurable] at translated
  exact translated

/-- A half-open interval splits at an interior point. -/
private theorem volume_split {region : Set Carrier} (measurable : borel.Measurable region)
    {lower middle upper : Carrier} (first : le lower middle) (second : le middle upper) :
    volume (Set.inter region (Ioc lower upper)) =
      ENNReal.add (volume (Set.inter region (Ioc lower middle)))
        (volume (Set.inter region (Ioc middle upper))) := by
  have union : Set.inter region (Ioc lower upper) =
      Set.union (Set.inter region (Ioc lower middle)) (Set.inter region (Ioc middle upper)) := by
    apply Set.ext
    intro value
    constructor
    · intro member
      by_cases left : le value middle
      · exact Or.inl ⟨member.1, member.2.1, left⟩
      · exact Or.inr ⟨member.1, not_le_iff_lt.mp left, member.2.2⟩
    · intro member
      rcases member with left | right
      · exact ⟨left.1, left.2.1, le_trans left.2.2 second⟩
      · exact ⟨right.1, lt_of_le_of_lt first right.2.1, right.2.2⟩
  rw [union]
  apply volume.union_disjoint (borel.inter measurable (measurable_ioc _ _))
    (borel.inter measurable (measurable_ioc _ _))
  intro value left right
  exact lt_irrefl value (lt_of_le_of_lt left.2.2 right.2.1)

public theorem turn_shift_measurable (shift : Carrier) :
    MeasurableMap borel (Space.product borel borel) (fun turns => turn (add shift turns)) :=
  MeasurableMap.comp turn_measurable (translate_measurable shift)

/-- A uniform turn shifted by `c ∈ [0, 1)` is still uniform on the circle. -/
public theorem circleLaw_shift {shift : Carrier} (lower : le zero shift) (upper : lt shift one) :
    restrictedUnit.map (fun turns => turn (add shift turns)) (turn_shift_measurable shift) =
      circleLaw := by
  apply Measure.ext
  intro region measurable
  let turned := Set.preimage turn region
  have turnedMeasurable : borel.Measurable turned := turn_measurable measurable
  have periodic : ∀ value, turned (add one value) ↔ turned value := by
    intro value
    change region (turn (add one value)) ↔ region (turn value)
    rw [add_comm, turn_add_one]
  rw [circleLaw, Measure.map_apply _ _ _ measurable, Measure.map_apply _ _ _ measurable,
    restrictedUnit, Measure.restrict_apply _ _ (turn_shift_measurable shift measurable),
    Measure.restrict_apply _ _ turnedMeasurable, unitSet, volume_inter_icc, volume_inter_icc]
  have moved : Set.inter (Set.preimage (fun turns => turn (add shift turns)) region) (Ioc zero one) =
      Set.preimage (add shift) (Set.inter turned (Ioc shift (add shift one))) := by
    apply Set.ext
    intro value
    change (turned (add shift value) ∧ lt zero value ∧ le value one) ↔
      (turned (add shift value) ∧ lt shift (add shift value) ∧ le (add shift value) (add shift one))
    constructor
    · intro member
      exact ⟨member.1, by real_grind, by real_grind⟩
    · intro member
      exact ⟨member.1, by real_grind, by real_grind⟩
  have wrapped : Set.preimage (add one) (Set.inter turned (Ioc one (add shift one))) =
      Set.inter turned (Ioc zero shift) := by
    apply Set.ext
    intro value
    change (turned (add one value) ∧ lt one (add one value) ∧ le (add one value) (add shift one)) ↔
      (turned value ∧ lt zero value ∧ le value shift)
    rw [periodic]
    constructor
    · intro member
      exact ⟨member.1, by real_grind, by real_grind⟩
    · intro member
      exact ⟨member.1, by real_grind, by real_grind⟩
  have inner := borel.inter turnedMeasurable (measurable_ioc one (add shift one))
  rw [moved, volume_preimage_translate shift (borel.inter turnedMeasurable (measurable_ioc _ _)),
    volume_split turnedMeasurable (le_of_lt upper) (by real_grind : le one (add shift one)),
    ← volume_preimage_translate one inner, wrapped,
    volume_split turnedMeasurable lower (le_of_lt upper), ENNReal.add_comm]

/-! ### Uniqueness -/

private theorem turnRotation_measurable :
    MeasurableMap (Space.product borel (Space.product borel borel)) (Space.product borel borel)
      (fun pair : Carrier × (Carrier × Carrier) =>
        rotation (turn pair.1).1 (turn pair.1).2 pair.2) := by
  have cosine : MeasurableMap (Space.product borel (Space.product borel borel)) borel
      (fun pair : Carrier × (Carrier × Carrier) => (turn pair.1).1) :=
    MeasurableMap.comp (Space.first_measurable borel borel)
      (MeasurableMap.comp turn_measurable (Space.first_measurable _ _))
  have sine : MeasurableMap (Space.product borel (Space.product borel borel)) borel
      (fun pair : Carrier × (Carrier × Carrier) => (turn pair.1).2) :=
    MeasurableMap.comp (Space.second_measurable borel borel)
      (MeasurableMap.comp turn_measurable (Space.first_measurable _ _))
  have horizontal : MeasurableMap (Space.product borel (Space.product borel borel)) borel
      (fun pair : Carrier × (Carrier × Carrier) => pair.2.1) :=
    MeasurableMap.comp (Space.first_measurable borel borel) (Space.second_measurable _ _)
  have vertical : MeasurableMap (Space.product borel (Space.product borel borel)) borel
      (fun pair : Carrier × (Carrier × Carrier) => pair.2.2) :=
    MeasurableMap.comp (Space.second_measurable borel borel) (Space.second_measurable _ _)
  unfold rotation
  apply Space.pair_measurable
  · exact measurable_sub (measurable_mul cosine horizontal) (measurable_mul sine vertical)
  · exact measurable_add (measurable_mul sine horizontal) (measurable_mul cosine vertical)

/-- The circle law is the only probability law on the plane that lives on the
unit circle and is kept by every rotation. -/
public theorem eq_circleLaw_of_rotation_invariant {law : Measure (Space.product borel borel)}
    (probability : Measure.IsProbability law)
    (onCircle : law.AE (fun point => squaredNorm point = one))
    (invariant : ∀ c s, squaredNorm (c, s) = one →
      law.map (rotation c s) (rotation_measurable c s) = law) :
    law = circleLaw := by
  apply Measure.ext
  intro region measurable
  let unitFinite := Measure.SFinite.ofFinite restrictedUnit_isProbability.to_finite
  let lawFinite := Measure.SFinite.ofFinite probability.to_finite
  let rotated : Set (Carrier × (Carrier × Carrier)) := Set.preimage
    (fun pair : Carrier × (Carrier × Carrier) => rotation (turn pair.1).1 (turn pair.1).2 pair.2) region
  have rotatedMeasurable := turnRotation_measurable measurable
  -- Integrating over the law first: each rotation keeps it.
  have byTurn : Measure.prod restrictedUnit law lawFinite rotated = law region := by
    rw [Measure.prod_apply _ _ _ rotatedMeasurable]
    have constant : (fun turns : Carrier =>
        law (Set.preimage (fun point => (turns, point)) rotated)) = fun _ => law region := by
      funext turns
      have kept := congrArg (fun measure : Measure (Space.product borel borel) => measure region)
        (invariant (turn turns).1 (turn turns).2 (squaredNorm_turn turns))
      rw [Measure.map_apply _ _ _ measurable] at kept
      exact kept
    rw [constant, lintegral_const, restrictedUnit_univ, ENNReal.mul_one]
  -- Integrating over the turn first: each point of the circle sees the circle law.
  have byPoint : Measure.prod restrictedUnit law lawFinite rotated = circleLaw region := by
    have swapped := congrArg (fun measure : Measure (Space.product (Space.product borel borel) borel) =>
        measure (Set.preimage (fun pair : (Carrier × Carrier) × Carrier => (pair.2, pair.1)) rotated))
      (Measure.prod_swap unitFinite lawFinite)
    have swappedMeasurable := Space.swap_measurable (Space.product borel borel) borel rotatedMeasurable
    rw [Measure.map_apply _ _ _ swappedMeasurable, Measure.prod_apply _ _ _ swappedMeasurable] at swapped
    refine Eq.trans ?_ (swapped.trans ?_)
    · rfl
    have pointwise : law.AEEq
        (fun point => restrictedUnit (Set.preimage (fun turns => (point, turns))
          (Set.preimage (fun pair : (Carrier × Carrier) × Carrier => (pair.2, pair.1)) rotated)))
        (fun _ => circleLaw region) := by
      apply Measure.AE.mono onCircle
      intro point unit
      obtain ⟨shift, lower, upper, atShift⟩ := turn_surjective unit
      rw [← circleLaw_shift lower upper, Measure.map_apply _ _ _ measurable]
      apply congrArg restrictedUnit
      apply Set.ext
      intro turns
      change region (rotation (turn turns).1 (turn turns).2 point) ↔ region (turn (add shift turns))
      rw [← atShift, rotation_turn, add_comm]
    · rw [lintegral_congr_ae pointwise, lintegral_const, probability.univ_eq_one, ENNReal.mul_one]
  exact byTurn.symm.trans byPoint

end

end Problib.Analysis
