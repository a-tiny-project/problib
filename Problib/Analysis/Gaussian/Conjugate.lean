module

public import Problib.Analysis.Gaussian.Density

/-! Gaussian conjugacy for the scalar normal-normal model.

A Gaussian prior at `(priorMean, priorVariance)` and a Gaussian likelihood in
the latent at `(latent, likelihoodVariance)`, read at an observation, multiply
to the evidence density at `(priorMean, priorVariance + likelihoodVariance)`
times a Gaussian density at the posterior parameters. Both variances are
runtime values and both must be positive. The identity is pointwise in the
latent, so a measure-level statement follows from it without a further analytic
premise.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Associativity and commutativity for the rewrite engine

The carrier's own `mul` and `add` are the ring operations, so declaring the two
structural laws lets `ac_rfl` normalize a polynomial after `simp` distributes
it. The instances are private and never leave this module.
-/

private instance : Std.Associative (α := Carrier) mul := ⟨fun l m r => mul_assoc l m r⟩
private instance : Std.Commutative (α := Carrier) mul := ⟨mul_comm⟩
private instance : Std.Associative (α := Carrier) add := ⟨fun l m r => add_assoc l m r⟩
private instance : Std.Commutative (α := Carrier) add := ⟨add_comm⟩

/-- Cancel one additive inverse appearing twice on the left. -/
private theorem cancel_twice (first second cross : Carrier) :
    add (add (add first (neg cross)) (add (neg cross) second)) (add cross cross) =
      add first second := by
  calc add (add (add first (neg cross)) (add (neg cross) second)) (add cross cross)
      = add (add first second) (add (add (neg cross) cross) (add (neg cross) cross)) := by ac_rfl
    _ = add (add first second) (add zero zero) := by
      rw [add_comm (neg cross) cross, add_neg]
    _ = add first second := by rw [add_zero, add_zero]

/-- A squared difference, stated additively so no cancellation is left open. -/
private theorem square_sub (left right : Carrier) :
    add (mul (sub left right) (sub left right)) (add (mul left right) (mul left right)) =
      add (mul left left) (mul right right) := by
  simp only [sub_eq_add_neg, mul_add, add_mul, neg_mul, mul_neg, neg_add, neg_neg,
    mul_comm right left]
  exact cancel_twice _ _ _

/-! ### The posterior parameters -/

/-- The posterior variance of a Gaussian observation of a Gaussian latent. -/
@[expose] public def posteriorVariance (priorVariance likelihoodVariance : Carrier) : Carrier :=
  div (mul priorVariance likelihoodVariance) (add priorVariance likelihoodVariance)

/-- The posterior mean: the precision-weighted average of observation and prior mean. -/
@[expose] public def posteriorMean
    (observation priorMean priorVariance likelihoodVariance : Carrier) : Carrier :=
  div (add (mul priorVariance observation) (mul likelihoodVariance priorMean))
    (add priorVariance likelihoodVariance)

public theorem posteriorVariance_positive {priorVariance likelihoodVariance : Carrier}
    (priorPositive : lt zero priorVariance) (likelihoodPositive : lt zero likelihoodVariance) :
    lt zero (posteriorVariance priorVariance likelihoodVariance) :=
  div_positive (mul_positive priorPositive likelihoodPositive)
    (add_positive priorPositive likelihoodPositive)

/-! ### The exponent identity

Write `u` for the latent's displacement from the prior mean and `w` for the
observation's displacement from the latent. Completing the square is then a
polynomial identity in five atoms, and clearing the four denominators once
turns the whole statement into that identity.
-/

/-- The two displacements add to the observation's displacement from the prior mean. -/
private theorem displacement_sum (observation priorMean latent : Carrier) :
    add (sub latent priorMean) (sub observation latent) = sub observation priorMean := by
  calc add (sub latent priorMean) (sub observation latent)
      = add (add latent (neg priorMean)) (add observation (neg latent)) := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
    _ = add (add latent (neg latent)) (add observation (neg priorMean)) := by ac_rfl
    _ = add zero (add observation (neg priorMean)) := by rw [add_neg]
    _ = sub observation priorMean := by
        rw [add_comm zero, add_zero, sub_eq_add_neg]

/-- The completing-the-square identity, with every denominator already cleared. -/
private theorem square_completion (priorVariance likelihoodVariance first second : Carrier) :
    add (mul (mul first first)
          (mul likelihoodVariance (add priorVariance likelihoodVariance)))
        (mul (mul second second)
          (mul priorVariance (add priorVariance likelihoodVariance))) =
      add (mul (mul (add first second) (add first second))
            (mul priorVariance likelihoodVariance))
        (mul (sub (mul likelihoodVariance first) (mul priorVariance second))
          (sub (mul likelihoodVariance first) (mul priorVariance second))) := by
  apply add_right_cancel (right := add
    (mul (mul likelihoodVariance first) (mul priorVariance second))
    (mul (mul likelihoodVariance first) (mul priorVariance second)))
  calc add (add (mul (mul first first)
            (mul likelihoodVariance (add priorVariance likelihoodVariance)))
          (mul (mul second second)
            (mul priorVariance (add priorVariance likelihoodVariance))))
        (add (mul (mul likelihoodVariance first) (mul priorVariance second))
          (mul (mul likelihoodVariance first) (mul priorVariance second)))
      = add (mul (mul (add first second) (add first second))
            (mul priorVariance likelihoodVariance))
          (add (mul (mul likelihoodVariance first) (mul likelihoodVariance first))
            (mul (mul priorVariance second) (mul priorVariance second))) := by
        simp only [mul_add, add_mul]
        ac_rfl
    _ = add (mul (mul (add first second) (add first second))
            (mul priorVariance likelihoodVariance))
          (add (mul (sub (mul likelihoodVariance first) (mul priorVariance second))
              (sub (mul likelihoodVariance first) (mul priorVariance second)))
            (add (mul (mul likelihoodVariance first) (mul priorVariance second))
              (mul (mul likelihoodVariance first) (mul priorVariance second)))) := by
        rw [square_sub]
    _ = add (add (mul (mul (add first second) (add first second))
            (mul priorVariance likelihoodVariance))
          (mul (sub (mul likelihoodVariance first) (mul priorVariance second))
            (sub (mul likelihoodVariance first) (mul priorVariance second))))
        (add (mul (mul likelihoodVariance first) (mul priorVariance second))
          (mul (mul likelihoodVariance first) (mul priorVariance second))) := by ac_rfl

private theorem div_mul_factor {denominator : Carrier} (numerator cofactor : Carrier)
    (nonzero : denominator ≠ zero) :
    mul (div numerator denominator) (mul denominator cofactor) = mul numerator cofactor := by
  rw [← mul_assoc, div_mul_cancel _ nonzero]

/-- The exponent the Gaussian density negates, before its normalizer. -/
private def exponent (mean variance value : Carrier) : Carrier :=
  div (mul (sub value mean) (sub value mean)) (mul (selection.ofRat 2) variance)

/-- Scaling the latent's displacement from the posterior mean by the summed
variance removes the division the posterior mean carries. -/
private theorem scaled_displacement (observation priorMean priorVariance likelihoodVariance
    latent : Carrier) (sumNonzero : add priorVariance likelihoodVariance ≠ zero) :
    mul (add priorVariance likelihoodVariance)
        (sub latent (posteriorMean observation priorMean priorVariance likelihoodVariance)) =
      sub (mul likelihoodVariance (sub latent priorMean))
        (mul priorVariance (sub observation latent)) := by
  rw [mul_sub, show mul (add priorVariance likelihoodVariance)
      (posteriorMean observation priorMean priorVariance likelihoodVariance) =
        add (mul priorVariance observation) (mul likelihoodVariance priorMean) from
      mul_div_cancel _ sumNonzero]
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, neg_add, neg_neg]
  ac_rfl

/-- Completing the square, with the four runtime denominators cleared once. -/
private theorem exponent_sum (observation priorMean priorVariance likelihoodVariance
    latent : Carrier) (priorPositive : lt zero priorVariance)
    (likelihoodPositive : lt zero likelihoodVariance) :
    add (exponent priorMean priorVariance latent)
        (exponent latent likelihoodVariance observation) =
      add (exponent priorMean (add priorVariance likelihoodVariance) observation)
        (exponent (posteriorMean observation priorMean priorVariance likelihoodVariance)
          (posteriorVariance priorVariance likelihoodVariance) latent) := by
  have sumPositive := add_positive priorPositive likelihoodPositive
  have variancePositive := posteriorVariance_positive priorPositive likelihoodPositive
  have priorNonzero := (positive_iff_nonnegative_and_nonzero.mp priorPositive).2
  have likelihoodNonzero := (positive_iff_nonnegative_and_nonzero.mp likelihoodPositive).2
  have sumNonzero := (positive_iff_nonnegative_and_nonzero.mp sumPositive).2
  have twoNonzero := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have priorScaled : mul (selection.ofRat 2) priorVariance ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive priorPositive)).2
  have likelihoodScaled : mul (selection.ofRat 2) likelihoodVariance ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive likelihoodPositive)).2
  have sumScaled : mul (selection.ofRat 2) (add priorVariance likelihoodVariance) ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive sumPositive)).2
  have varianceScaled : mul (selection.ofRat 2)
      (posteriorVariance priorVariance likelihoodVariance) ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive variancePositive)).2
  have factorNonzero : mul (selection.ofRat 2) (mul priorVariance
      (mul likelihoodVariance (add priorVariance likelihoodVariance))) ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive
      (mul_positive priorPositive (mul_positive likelihoodPositive sumPositive)))).2
  apply mul_right_cancel_of_nonzero factorNonzero
  have varianceProduct : mul (posteriorVariance priorVariance likelihoodVariance)
      (add priorVariance likelihoodVariance) = mul priorVariance likelihoodVariance :=
    div_mul_cancel _ sumNonzero
  have firstFactor : mul (selection.ofRat 2) (mul priorVariance
      (mul likelihoodVariance (add priorVariance likelihoodVariance))) =
      mul (mul (selection.ofRat 2) priorVariance)
        (mul likelihoodVariance (add priorVariance likelihoodVariance)) := by ac_rfl
  have secondFactor : mul (selection.ofRat 2) (mul priorVariance
      (mul likelihoodVariance (add priorVariance likelihoodVariance))) =
      mul (mul (selection.ofRat 2) likelihoodVariance)
        (mul priorVariance (add priorVariance likelihoodVariance)) := by ac_rfl
  have thirdFactor : mul (selection.ofRat 2) (mul priorVariance
      (mul likelihoodVariance (add priorVariance likelihoodVariance))) =
      mul (mul (selection.ofRat 2) (add priorVariance likelihoodVariance))
        (mul priorVariance likelihoodVariance) := by ac_rfl
  have fourthFactor : mul (selection.ofRat 2) (mul priorVariance
      (mul likelihoodVariance (add priorVariance likelihoodVariance))) =
      mul (mul (selection.ofRat 2) (posteriorVariance priorVariance likelihoodVariance))
        (mul (add priorVariance likelihoodVariance) (add priorVariance likelihoodVariance)) := by
    calc mul (selection.ofRat 2) (mul priorVariance
          (mul likelihoodVariance (add priorVariance likelihoodVariance)))
        = mul (selection.ofRat 2) (mul (mul priorVariance likelihoodVariance)
          (add priorVariance likelihoodVariance)) := by ac_rfl
      _ = mul (selection.ofRat 2) (mul (mul (posteriorVariance priorVariance likelihoodVariance)
            (add priorVariance likelihoodVariance)) (add priorVariance likelihoodVariance)) := by
          rw [varianceProduct]
      _ = _ := by ac_rfl
  rw [add_mul, add_mul, exponent, exponent, exponent, exponent]
  rw [show mul (div (mul (sub latent priorMean) (sub latent priorMean))
        (mul (selection.ofRat 2) priorVariance)) (mul (selection.ofRat 2) (mul priorVariance
        (mul likelihoodVariance (add priorVariance likelihoodVariance)))) =
      mul (mul (sub latent priorMean) (sub latent priorMean))
        (mul likelihoodVariance (add priorVariance likelihoodVariance)) from by
    rw [firstFactor]; exact div_mul_factor _ _ priorScaled]
  rw [show mul (div (mul (sub observation latent) (sub observation latent))
        (mul (selection.ofRat 2) likelihoodVariance)) (mul (selection.ofRat 2) (mul priorVariance
        (mul likelihoodVariance (add priorVariance likelihoodVariance)))) =
      mul (mul (sub observation latent) (sub observation latent))
        (mul priorVariance (add priorVariance likelihoodVariance)) from by
    rw [secondFactor]; exact div_mul_factor _ _ likelihoodScaled]
  rw [show mul (div (mul (sub observation priorMean) (sub observation priorMean))
        (mul (selection.ofRat 2) (add priorVariance likelihoodVariance)))
        (mul (selection.ofRat 2) (mul priorVariance
        (mul likelihoodVariance (add priorVariance likelihoodVariance)))) =
      mul (mul (sub observation priorMean) (sub observation priorMean))
        (mul priorVariance likelihoodVariance) from by
    rw [thirdFactor]; exact div_mul_factor _ _ sumScaled]
  rw [show mul (div (mul (sub latent (posteriorMean observation priorMean priorVariance
          likelihoodVariance)) (sub latent (posteriorMean observation priorMean priorVariance
          likelihoodVariance))) (mul (selection.ofRat 2)
        (posteriorVariance priorVariance likelihoodVariance)))
        (mul (selection.ofRat 2) (mul priorVariance
        (mul likelihoodVariance (add priorVariance likelihoodVariance)))) =
      mul (mul (sub latent (posteriorMean observation priorMean priorVariance likelihoodVariance))
          (sub latent (posteriorMean observation priorMean priorVariance likelihoodVariance)))
        (mul (add priorVariance likelihoodVariance) (add priorVariance likelihoodVariance)) from by
    rw [fourthFactor]; exact div_mul_factor _ _ varianceScaled]
  rw [show mul (mul (sub latent (posteriorMean observation priorMean priorVariance
          likelihoodVariance)) (sub latent (posteriorMean observation priorMean priorVariance
          likelihoodVariance)))
        (mul (add priorVariance likelihoodVariance) (add priorVariance likelihoodVariance)) =
      mul (sub (mul likelihoodVariance (sub latent priorMean))
          (mul priorVariance (sub observation latent)))
        (sub (mul likelihoodVariance (sub latent priorMean))
          (mul priorVariance (sub observation latent))) from by
    rw [← scaled_displacement observation priorMean priorVariance likelihoodVariance latent
      sumNonzero]
    ac_rfl]
  rw [← displacement_sum observation priorMean latent]
  exact square_completion priorVariance likelihoodVariance (sub latent priorMean)
    (sub observation latent)

/-! ### The normalizer identity

The two normalizers on each side agree exactly, because the posterior variance
times the summed variance is the product of the two input variances. No
approximation and no positivity of the observation enter here.
-/

private theorem nonnegative_ofReal_mul {left right : Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    NNReal.ofReal (mul left right) = NNReal.mul (NNReal.ofReal left) (NNReal.ofReal right) := by
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal leftNonnegative,
    NNReal.toReal_ofReal rightNonnegative,
    NNReal.toReal_ofReal (mul_nonnegative leftNonnegative rightNonnegative)]

/-- The prior and likelihood normalizers multiply to the evidence and posterior
normalizers. -/
public theorem normalizer_product {priorVariance likelihoodVariance : Carrier}
    (priorPositive : lt zero priorVariance) (likelihoodPositive : lt zero likelihoodVariance) :
    NNReal.mul (normalizer priorVariance) (normalizer likelihoodVariance) =
      NNReal.mul (normalizer (add priorVariance likelihoodVariance))
        (normalizer (posteriorVariance priorVariance likelihoodVariance)) := by
  have sumPositive := add_positive priorPositive likelihoodPositive
  have variancePositive := posteriorVariance_positive priorPositive likelihoodPositive
  have sumNonzero := (positive_iff_nonnegative_and_nonzero.mp sumPositive).2
  have varianceProduct : mul (posteriorVariance priorVariance likelihoodVariance)
      (add priorVariance likelihoodVariance) = mul priorVariance likelihoodVariance :=
    div_mul_cancel _ sumNonzero
  have scale : le zero (mul (selection.ofRat 2) pi) :=
    (mul_positive ofRat_two_positive pi_positive).1
  have product : mul (mul (mul (selection.ofRat 2) pi) priorVariance)
      (mul (mul (selection.ofRat 2) pi) likelihoodVariance) =
      mul (mul (mul (selection.ofRat 2) pi) (add priorVariance likelihoodVariance))
        (mul (mul (selection.ofRat 2) pi)
          (posteriorVariance priorVariance likelihoodVariance)) := by
    calc mul (mul (mul (selection.ofRat 2) pi) priorVariance)
          (mul (mul (selection.ofRat 2) pi) likelihoodVariance)
        = mul (mul (mul (selection.ofRat 2) pi) (mul (selection.ofRat 2) pi))
            (mul priorVariance likelihoodVariance) := by ac_rfl
      _ = mul (mul (mul (selection.ofRat 2) pi) (mul (selection.ofRat 2) pi))
            (mul (posteriorVariance priorVariance likelihoodVariance)
              (add priorVariance likelihoodVariance)) := by rw [varianceProduct]
      _ = _ := by ac_rfl
  unfold normalizer
  rw [← sqrt_mul, ← sqrt_mul,
    ← nonnegative_ofReal_mul (mul_nonnegative scale priorPositive.1)
      (mul_nonnegative scale likelihoodPositive.1),
    ← nonnegative_ofReal_mul (mul_nonnegative scale sumPositive.1)
      (mul_nonnegative scale variancePositive.1), product]

/-! ### The pointwise conjugacy identity -/

private instance : Std.Associative (α := NNReal) NNReal.mul :=
  ⟨fun l m r => NNReal.mul_assoc l m r⟩
private instance : Std.Commutative (α := NNReal) NNReal.mul := ⟨NNReal.mul_comm⟩

private theorem density_eq_div (mean variance value : Carrier) :
    density mean variance value =
      NNReal.div (NNReal.ofReal (exp (neg (exponent mean variance value))))
        (normalizer variance) := by
  apply NNReal.ext
  rw [density_toReal, NNReal.toReal_div, NNReal.toReal_ofReal (exp_positive _).1]
  rfl

private theorem exponential_product (first second : Carrier) :
    NNReal.mul (NNReal.ofReal (exp (neg first))) (NNReal.ofReal (exp (neg second))) =
      NNReal.ofReal (exp (neg (add first second))) := by
  rw [← nonnegative_ofReal_mul (exp_positive _).1 (exp_positive _).1, ← exp_add, neg_add]

/-- Gaussian conjugacy, pointwise in the latent. A Gaussian prior density at
`(priorMean, priorVariance)` times a Gaussian likelihood density in the latent
at `(latent, likelihoodVariance)`, read at the observation, equals the evidence
density at `(priorMean, priorVariance + likelihoodVariance)` times the Gaussian
density at the posterior parameters. Both variances must be positive; the
observation, the prior mean and the latent are arbitrary. -/
public theorem density_conjugate {priorVariance likelihoodVariance : Carrier}
    (priorPositive : lt zero priorVariance) (likelihoodPositive : lt zero likelihoodVariance)
    (observation priorMean latent : Carrier) :
    NNReal.mul (density priorMean priorVariance latent)
        (density latent likelihoodVariance observation) =
      NNReal.mul (density priorMean (add priorVariance likelihoodVariance) observation)
        (density (posteriorMean observation priorMean priorVariance likelihoodVariance)
          (posteriorVariance priorVariance likelihoodVariance) latent) := by
  have sumPositive := add_positive priorPositive likelihoodPositive
  have variancePositive := posteriorVariance_positive priorPositive likelihoodPositive
  have priorNonzero := (NNReal.zero_lt_iff_ne_zero _).mp (normalizer_positive _ priorPositive)
  have likelihoodNonzero := (NNReal.zero_lt_iff_ne_zero _).mp (normalizer_positive _ likelihoodPositive)
  have sumNonzero := (NNReal.zero_lt_iff_ne_zero _).mp (normalizer_positive _ sumPositive)
  have varianceNonzero := (NNReal.zero_lt_iff_ne_zero _).mp (normalizer_positive _ variancePositive)
  have productNonzero : NNReal.mul (normalizer priorVariance) (normalizer likelihoodVariance) ≠
      NNReal.zero := by
    intro vanished
    rcases NNReal.mul_eq_zero_iff.mp vanished with left | right
    · exact priorNonzero left
    · exact likelihoodNonzero right
  apply NNReal.mul_right_cancel productNonzero
  rw [density_eq_div priorMean priorVariance latent,
    density_eq_div latent likelihoodVariance observation,
    density_eq_div priorMean (add priorVariance likelihoodVariance) observation,
    density_eq_div (posteriorMean observation priorMean priorVariance likelihoodVariance)
      (posteriorVariance priorVariance likelihoodVariance) latent]
  calc NNReal.mul (NNReal.mul
          (NNReal.div (NNReal.ofReal (exp (neg (exponent priorMean priorVariance latent))))
            (normalizer priorVariance))
          (NNReal.div (NNReal.ofReal (exp (neg (exponent latent likelihoodVariance observation))))
            (normalizer likelihoodVariance)))
        (NNReal.mul (normalizer priorVariance) (normalizer likelihoodVariance))
      = NNReal.mul
          (NNReal.mul (NNReal.div (NNReal.ofReal
              (exp (neg (exponent priorMean priorVariance latent)))) (normalizer priorVariance))
            (normalizer priorVariance))
          (NNReal.mul (NNReal.div (NNReal.ofReal
              (exp (neg (exponent latent likelihoodVariance observation))))
            (normalizer likelihoodVariance)) (normalizer likelihoodVariance)) := by ac_rfl
    _ = NNReal.mul (NNReal.ofReal (exp (neg (exponent priorMean priorVariance latent))))
          (NNReal.ofReal (exp (neg (exponent latent likelihoodVariance observation)))) := by
        rw [NNReal.div_mul_cancel _ priorNonzero, NNReal.div_mul_cancel _ likelihoodNonzero]
    _ = NNReal.ofReal (exp (neg (add (exponent priorMean priorVariance latent)
          (exponent latent likelihoodVariance observation)))) := exponential_product _ _
    _ = NNReal.ofReal (exp (neg (add
          (exponent priorMean (add priorVariance likelihoodVariance) observation)
          (exponent (posteriorMean observation priorMean priorVariance likelihoodVariance)
            (posteriorVariance priorVariance likelihoodVariance) latent)))) := by
        rw [exponent_sum observation priorMean priorVariance likelihoodVariance latent
          priorPositive likelihoodPositive]
    _ = NNReal.mul (NNReal.ofReal
          (exp (neg (exponent priorMean (add priorVariance likelihoodVariance) observation))))
          (NNReal.ofReal (exp (neg (exponent
            (posteriorMean observation priorMean priorVariance likelihoodVariance)
            (posteriorVariance priorVariance likelihoodVariance) latent)))) :=
        (exponential_product _ _).symm
    _ = NNReal.mul
          (NNReal.mul (NNReal.div (NNReal.ofReal (exp (neg (exponent priorMean
              (add priorVariance likelihoodVariance) observation))))
            (normalizer (add priorVariance likelihoodVariance)))
            (normalizer (add priorVariance likelihoodVariance)))
          (NNReal.mul (NNReal.div (NNReal.ofReal (exp (neg (exponent
              (posteriorMean observation priorMean priorVariance likelihoodVariance)
              (posteriorVariance priorVariance likelihoodVariance) latent))))
            (normalizer (posteriorVariance priorVariance likelihoodVariance)))
            (normalizer (posteriorVariance priorVariance likelihoodVariance))) := by
        rw [NNReal.div_mul_cancel _ sumNonzero, NNReal.div_mul_cancel _ varianceNonzero]
    _ = NNReal.mul (NNReal.mul
          (NNReal.div (NNReal.ofReal (exp (neg (exponent priorMean
            (add priorVariance likelihoodVariance) observation))))
            (normalizer (add priorVariance likelihoodVariance)))
          (NNReal.div (NNReal.ofReal (exp (neg (exponent
            (posteriorMean observation priorMean priorVariance likelihoodVariance)
            (posteriorVariance priorVariance likelihoodVariance) latent))))
            (normalizer (posteriorVariance priorVariance likelihoodVariance))))
        (NNReal.mul (normalizer (add priorVariance likelihoodVariance))
          (normalizer (posteriorVariance priorVariance likelihoodVariance))) := by ac_rfl
    _ = _ := by rw [← normalizer_product priorPositive likelihoodPositive]

/-- The posterior-to-prior density ratio at a latent is the likelihood over the
evidence. The normalizers' π cancels on both sides. -/
public theorem density_ratio {priorVariance likelihoodVariance : Carrier}
    (priorPositive : lt zero priorVariance) (likelihoodPositive : lt zero likelihoodVariance)
    (observation priorMean latent : Carrier) :
    NNReal.div
        (density (posteriorMean observation priorMean priorVariance likelihoodVariance)
          (posteriorVariance priorVariance likelihoodVariance) latent)
        (density priorMean priorVariance latent) =
      NNReal.div (density latent likelihoodVariance observation)
        (density priorMean (add priorVariance likelihoodVariance) observation) := by
  have priorNonzero := (NNReal.zero_lt_iff_ne_zero _).mp
    (density_positive priorMean priorVariance priorPositive latent)
  have evidenceNonzero := (NNReal.zero_lt_iff_ne_zero _).mp
    (density_positive priorMean _ (add_positive priorPositive likelihoodPositive) observation)
  apply NNReal.mul_right_cancel priorNonzero
  apply NNReal.mul_left_cancel evidenceNonzero
  rw [NNReal.div_mul_cancel _ priorNonzero,
    ← density_conjugate priorPositive likelihoodPositive observation priorMean latent,
    ← NNReal.mul_assoc, NNReal.mul_div_cancel _ evidenceNonzero, NNReal.mul_comm]

end
end Problib.Analysis.Gaussian
