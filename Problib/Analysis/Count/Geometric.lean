module

public import Problib.Analysis.Count.Basic
public import Problib.Analysis.Gamma.Exponential
public import Problib.Analysis.RealPower
public import Problib.Analysis.Real.PowerSeries.Reciprocal

/-! The geometric law on the naturals.

At a success probability `p` with `0 < p ≤ 1`, the geometric law counts the
failures before the first success: it gives the count `k` the mass `p(1-p)^k`
(`mass`). At `p = 1` that mass is the Dirac law at zero, since `(1-p)^k`
vanishes past `k = 0`. At `p ≤ 0` no success ever comes and the count has no
law on the naturals. `law` takes the Dirac law at zero there, the law the
sampler `natFloor(log(1-u) / log(1-p))` has once the logarithm of one, zero,
divides it (`law_of_nonpositive`).

The law is the floor of an exponential law (`exponential_map_floor`). At
`0 < p < 1` the rate `-log(1-p)` is positive (`rate_positive`), and the
exponential law at that rate puts `e^(-rate k) - e^(-rate (k+1))`, which is
`(1-p)^k - (1-p)^(k+1)`, between `k` and `k + 1`. Any floor on the naturals
(`IsFloor`) pushes it forward to `law`. The masses sum to one by the geometric
series, so the law is a probability measure at every `p` in the unit interval
(`law_isProbability`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Count.Geometric

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Logarithm
open Problib.Analysis.Real.SignedSeries (power power_zero power_succ power_nonnegative)

noncomputable section

/-- The geometric mass `p(1-p)^k` at a positive success probability, and the
Dirac mass at zero otherwise. -/
@[expose] public def mass (success : Carrier) (count : Nat) : NNReal := by
  classical
  exact if lt zero success then NNReal.ofReal (mul success (power (sub one success) count))
    else if count = 0 then NNReal.one else NNReal.zero

/-- The geometric law: the count `k` has mass `mass success k`. -/
@[expose] public def law (success : Carrier) : Measure (Space.discrete Nat) :=
  ofMass (mass success)

public theorem mass_of_positive {success : Carrier} (positive : lt zero success) (count : Nat) :
    mass success count = NNReal.ofReal (mul success (power (sub one success) count)) := by
  unfold mass
  exact ite_eq_left positive

public theorem mass_of_nonpositive {success : Carrier} (nonpositive : ¬lt zero success)
    (count : Nat) : mass success count = if count = 0 then NNReal.one else NNReal.zero := by
  unfold mass
  exact ite_eq_right nonpositive

/-- The law gives each count its mass. -/
public theorem law_singleton (success : Carrier) (count : Nat) :
    law success (fun value => value = count) = ENNReal.finite (mass success count) :=
  ofMass_singleton _ count

/-- A law on `ℕ` whose masses are one at zero and zero elsewhere is the Dirac
law at zero. -/
private theorem dirac_of_mass {masses : Nat → NNReal}
    (point : ∀ count, masses count = if count = 0 then NNReal.one else NNReal.zero) :
    ofMass masses = Measure.dirac _ 0 := by
  apply ext_singleton
  intro count
  rw [ofMass_singleton, point count]
  by_cases zero : count = 0
  · subst zero
    rw [ite_eq_left rfl, Measure.dirac_apply_of_mem (Space.discrete Nat) 0
      (set := fun value => value = 0) (Space.discrete_measurable _) rfl]
    rfl
  · rw [ite_eq_right zero, Measure.dirac_apply_of_not_mem (Space.discrete Nat) 0
      (set := fun value => value = count) (Space.discrete_measurable _)
      (fun equal => zero equal.symm)]
    rfl

/-- At a nonpositive success probability the law is the Dirac law at zero. -/
public theorem law_of_nonpositive {success : Carrier} (nonpositive : ¬lt zero success) :
    law success = Measure.dirac _ 0 :=
  dirac_of_mass (mass_of_nonpositive nonpositive)

/-- At success probability zero the law is the Dirac law at zero. -/
public theorem law_zero : law zero = Measure.dirac _ 0 :=
  law_of_nonpositive (lt_irrefl zero)

/-- At success probability one every trial succeeds, so the law is the Dirac
law at zero. -/
public theorem law_one : law one = Measure.dirac _ 0 := by
  apply dirac_of_mass
  intro count
  rw [mass_of_positive one_positive, sub_self, one_mul]
  cases count with
  | zero =>
      rw [power_zero, ite_eq_left rfl]
      exact NNReal.ext (by rw [NNReal.toReal_ofReal (le_of_lt one_positive), NNReal.toReal_one])
  | succ count =>
      rw [power_succ, zero_mul, ite_eq_right (Nat.succ_ne_zero count)]
      exact NNReal.ofReal_zero

/-! ### The floor of an exponential law -/

/-- A natural as a real. -/
@[expose] public def natReal (count : Nat) : Carrier := selection.ofRat (count : Rat)

/-- `floor` takes each real to the least `n` it lies below `n + 1` of: its floor
at a nonnegative real, and zero below. -/
@[expose] public def IsFloor (floor : Carrier → Nat) : Prop :=
  ∀ value count, floor value = count ↔
    lt value (natReal (count + 1)) ∧ ∀ smaller, smaller < count → ¬lt value (natReal (smaller + 1))

/-- The exponential rate of the geometric law, `-log(1-p)`. -/
@[expose] public def rate (success : Carrier) : Carrier := neg (logIntegral (sub one success))

/-- The failure probability `1 - p` lies strictly between zero and one. -/
private theorem failure_between {success : Carrier} (positive : lt zero success)
    (belowOne : lt success one) :
    lt zero (sub one success) ∧ lt (sub one success) one := by
  constructor
  · exact sub_positive_iff.mpr belowOne
  · have shifted := sub_positive_iff.mpr (show lt (sub one success) one from by
      rw [← sub_positive_iff, sub_sub_cancel]
      exact positive)
    exact sub_positive_iff.mp shifted

public theorem rate_positive {success : Carrier} (positive : lt zero success)
    (belowOne : lt success one) : lt zero (rate success) := by
  obtain ⟨failurePositive, failureBelow⟩ := failure_between positive belowOne
  have logged := log_strict _ _ failurePositive failureBelow
  rw [log_one] at logged
  unfold rate
  rw [← neg_zero]
  exact neg_lt_neg_iff.mpr logged

/-- The exponential tail at a count is the failure probability's power. -/
public theorem exp_rate {success : Carrier} (positive : lt zero success)
    (belowOne : lt success one) (count : Nat) :
    exp (neg (mul (rate success) (natReal count))) = power (sub one success) count := by
  obtain ⟨failurePositive, _⟩ := failure_between positive belowOne
  unfold rate natReal
  rw [neg_mul, neg_neg, mul_comm, ← rpow_of_positive failurePositive,
    rpow_nat failurePositive.1 count]

/-- The tail at zero is one. -/
private theorem exp_rate_zero (success : Carrier) :
    exp (neg (mul (rate success) (natReal 0))) = one := by
  have cast : ((0 : Nat) : Rat) = 0 := rfl
  unfold natReal
  rw [cast, ofRat_zero, mul_zero, neg_zero, exp_zero]

/-- A positive real's exponential tail is at most one. -/
private theorem tail_le_one {rate threshold : Carrier} (ratePositive : lt zero rate)
    (positive : lt zero threshold) : le (exp (neg (mul rate threshold))) one := by
  rw [← exp_zero]
  apply exp_monotone
  rw [← neg_zero]
  exact neg_le_neg_iff.mpr (mul_positive ratePositive positive).1

/-- The exponential law between two positive thresholds. -/
private theorem law_slab {rate lower upper : Carrier} (ratePositive : lt zero rate)
    (lowerPositive : lt zero lower) (ordered : le lower upper) :
    Gamma.law one rate (Set.inter (Iio upper) (Set.complement (Iio lower))) =
      ENNReal.ofReal (sub (exp (neg (mul rate lower))) (exp (neg (mul rate upper)))) := by
  have upperPositive : lt zero upper := lt_of_lt_of_le lowerPositive ordered
  have cover : Set.union (Iio lower) (Set.inter (Iio upper) (Set.complement (Iio lower))) =
      Iio upper :=
    Set.ext fun value => ⟨fun member => member.elim (fun below => lt_of_lt_of_le below ordered)
        (fun slab => slab.1),
      fun below => (Classical.em (lt value lower)).elim Or.inl fun above => Or.inr ⟨below, above⟩⟩
  have split := Measure.union_disjoint (Gamma.law one rate) (measurable_iio lower)
    (Space.inter _ (measurable_iio upper) (Space.complement _ (measurable_iio lower)))
    fun _ below slab => slab.2 below
  rw [cover, Gamma.law_one_iio ratePositive upperPositive,
    Gamma.law_one_iio ratePositive lowerPositive] at split
  have decayed : le (exp (neg (mul rate upper))) (exp (neg (mul rate lower))) := by
    apply exp_monotone
    exact neg_le_neg_iff.mpr ((mul_le_mul_left_iff ratePositive).mpr ordered)
  have parts := ENNReal.ofReal_add (sub_nonnegative (tail_le_one ratePositive lowerPositive))
    (sub_nonnegative decayed)
  have telescope : add (sub one (exp (neg (mul rate lower))))
      (sub (exp (neg (mul rate lower))) (exp (neg (mul rate upper)))) =
      sub one (exp (neg (mul rate upper))) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_assoc,
      ← add_assoc (neg (exp (neg (mul rate lower)))), add_comm (neg (exp (neg (mul rate lower)))),
      add_neg, zero_add]
  rw [telescope, split] at parts
  exact (ENNReal.add_left_cancel_of_finite (ENNReal.ofReal_finite _) parts)

/-- Under a floor, the reals that floor to a count are those below it plus one
and not below it. -/
private theorem floor_fibre {floor : Carrier → Nat} (isFloor : IsFloor floor) (count : Nat) :
    (fun value => floor value = count + 1) =
      Set.inter (Iio (natReal (count + 2))) (Set.complement (Iio (natReal (count + 1)))) := by
  apply Set.ext
  intro value
  rw [isFloor value (count + 1)]
  constructor
  · intro ⟨below, least⟩
    exact ⟨below, least count (Nat.lt_succ_self count)⟩
  · intro ⟨below, above⟩
    refine ⟨below, fun smaller less earlier => above ?_⟩
    refine lt_of_lt_of_le earlier ?_
    unfold natReal
    rw [ofRat_le_iff]
    exact Rat.natCast_le_natCast.mpr (by omega)

/-- Under a floor, the reals that floor to zero are those below one. -/
private theorem floor_fibre_zero {floor : Carrier → Nat} (isFloor : IsFloor floor) :
    (fun value => floor value = 0) = Iio (natReal 1) := by
  apply Set.ext
  intro value
  rw [isFloor value 0]
  exact ⟨fun held => held.1, fun below => ⟨below, fun _ less => absurd less (Nat.not_lt_zero _)⟩⟩

private theorem natReal_positive (count : Nat) : lt zero (natReal (count + 1)) := by
  unfold natReal
  rw [← ofRat_zero, ofRat_lt_iff]
  exact Rat.natCast_pos.mpr (Nat.succ_pos count)

/-- The mass at a count is the difference of consecutive failure powers. -/
private theorem mass_difference (success : Carrier) (count : Nat) :
    mul success (power (sub one success) count) =
      sub (power (sub one success) count) (power (sub one success) (count + 1)) := by
  rw [power_succ]
  conv => rhs; arg 1; rw [← one_mul (power (sub one success) count)]
  rw [← sub_mul, sub_sub_cancel]

/-- Pushing the exponential law at rate `-log(1-p)` through a floor gives the
geometric law, at every `p` strictly between zero and one. -/
public theorem exponential_map_floor {success : Carrier} (positive : lt zero success)
    (belowOne : lt success one) {floor : Carrier → Nat} (isFloor : IsFloor floor)
    (measurable : MeasurableMap borel (Space.discrete Nat) floor) :
    (Gamma.law one (rate success)).map floor measurable = law success := by
  have ratePositive := rate_positive positive belowOne
  apply ext_singleton
  intro count
  rw [Measure.map_apply _ _ _ (Space.discrete_measurable _), law_singleton,
    mass_of_positive positive, mass_difference success]
  show Gamma.law one (rate success) (fun value => floor value = count) = _
  cases count with
  | zero =>
      rw [floor_fibre_zero isFloor, Gamma.law_one_iio ratePositive (natReal_positive 0),
        ← exp_rate_zero success, exp_rate positive belowOne 0, exp_rate positive belowOne 1]
      rfl
  | succ count =>
      rw [floor_fibre isFloor count]
      show Gamma.law one (rate success) (Set.inter (Iio (natReal (count + 1 + 1)))
        (Set.complement (Iio (natReal (count + 1))))) = _
      rw [law_slab (upper := natReal (count + 1 + 1)) ratePositive (natReal_positive count)
        (le_of_lt ((ofRat_lt_iff _ _).mpr (Rat.natCast_lt_natCast.mpr (Nat.lt_succ_self _)))),
        exp_rate positive belowOne, exp_rate positive belowOne]
      rfl

/-- At a positive success probability the masses sum to one: `p` times the
geometric series `1/(1 - (1 - p))`. -/
private theorem masses_converge {success : Carrier} (positive : lt zero success)
    (atMostOne : le success one) :
    Problib.Analysis.Real.ConvergesTo
      (Problib.Analysis.Real.SignedSeries.partialSum fun count =>
        mul success (power (sub one success) count)) one := by
  have failureNonnegative : le zero (sub one success) := sub_nonnegative atMostOne
  have belowOne : lt (Problib.Analysis.Real.abs (sub one success)) one := by
    rw [Problib.Analysis.Real.abs_of_nonnegative failureNonnegative, ← sub_positive_iff,
      sub_sub_cancel]
    exact positive
  have scaled := Problib.Analysis.Real.SignedSeries.converges_to_scale success
    (Problib.Analysis.Real.SignedSeries.partialSum_converges (power (sub one success))
      (Problib.Analysis.Real.SignedSeries.geometric_summable_of_abs_lt_one belowOne))
  rw [Problib.Analysis.Real.PowerSeries.geometric_sum belowOne, sub_sub_cancel,
    mul_inverse_cancel (fun vanishing => by rw [vanishing] at positive; exact lt_irrefl zero positive)] at scaled
  exact (congrArg (fun values => Problib.Analysis.Real.ConvergesTo values one)
    (funext fun count =>
      (Problib.Analysis.Real.SignedSeries.partialSum_scale success _ count).symm)).mp scaled

/-- The geometric law is a probability measure at every success probability in
the unit interval. -/
public theorem law_isProbability (success : UnitInterval) :
    Measure.IsProbability (law success.val) := by
  by_cases positive : lt zero success.val
  · have masses : mass success.val = fun count =>
        NNReal.ofReal (mul success.val (power (sub one success.val) count)) :=
      funext (mass_of_positive positive)
    unfold law
    rw [masses]
    exact ofMass_isProbability
      (fun count => mul_nonnegative positive.1 (power_nonnegative
        (sub_nonnegative success.property.2) count))
      (masses_converge positive success.property.2)
  · rw [law_of_nonpositive positive]
    exact Measure.IsProbability.dirac _ 0

end

end Problib.Analysis.Count.Geometric
