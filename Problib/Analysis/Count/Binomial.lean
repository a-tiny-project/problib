module

public import Problib.Analysis.Count.Basic
public import Problib.Analysis.Real.GeometricSeries
public import Problib.Analysis.Real.FactorialSeries
public import Problib.Real.Grind
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Extended.Conversion
public import Problib.Analysis.RealPower

/-! The binomial law on the naturals.

`n` independent trials that each succeed with probability `p` give `k`
successes with probability `C(n, k) p^k (1 - p)^(n - k)`, and none past `n`
(`law_singleton`). The binomial coefficient `choose` is defined by Pascal's
rule, so the masses at `n + 1` trials split into the masses at `n` trials after
a success and after a failure (`term_succ`). Summing that split gives the
binomial theorem `Σ_k C(n, k) p^k (1 - p)^(n - k) = 1` at every `p`
(`term_sum`), so the law is a probability measure on `0 ≤ p ≤ 1`
(`law_isProbability`). At `p = 0` and `p = 1` it is the point mass at `0` and at
`n` (`law_zero`, `law_one`).

The coefficient meets the factorial series through
`C(n, k) (1/n!) = (1/k!) (1/(n - k)!)` (`choose_factorialTerm`), the form in
which `lgamma` reads factorials (`lgamma_nat`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Count.Binomial

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm partialSum partialSum_succ power power_zero
  power_succ power_nonnegative partialSum_zero_after factorialTerm_one_positive)
open Problib.Analysis.Logarithm (logIntegral)

noncomputable section

/-! ### The binomial coefficient -/

/-- The binomial coefficient, by Pascal's rule. -/
@[expose] public def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | count + 1, chosen + 1 => choose count chosen + choose count (chosen + 1)

public theorem choose_zero_right (count : Nat) : choose count 0 = 1 := by
  cases count <;> rfl

public theorem choose_succ_succ (count chosen : Nat) :
    choose (count + 1) (chosen + 1) = choose count chosen + choose count (chosen + 1) := rfl

/-- No way chooses more than there are. -/
public theorem choose_of_lt : ∀ {count chosen : Nat}, count < chosen → choose count chosen = 0
  | 0, _ + 1, _ => rfl
  | count + 1, chosen + 1, less => by
      rw [choose_succ_succ, choose_of_lt (Nat.lt_of_succ_lt_succ less),
        choose_of_lt (Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ less))]

public theorem choose_self : ∀ count : Nat, choose count count = 1
  | 0 => rfl
  | count + 1 => by
      rw [choose_succ_succ, choose_self count, choose_of_lt (Nat.lt_succ_self count)]

/-- A natural number as a real. -/
private abbrev natural (count : Nat) : Carrier := selection.ofRat (count : Rat)

private theorem natural_add (first second : Nat) :
    natural (first + second) = add (natural first) (natural second) := by
  show selection.ofRat ((first + second : Nat) : Rat) = _
  rw [Rat.natCast_add, ofRat_add]

private theorem natural_one : natural 1 = one := ofRat_one

private theorem natural_zero : natural 0 = zero := ofRat_zero

private theorem natural_nonnegative (count : Nat) : le zero (natural count) := by
  rw [← ofRat_zero]
  exact (ofRat_le_iff 0 (count : Rat)).mpr Rat.natCast_nonneg

private theorem natural_succ_positive (count : Nat) : lt zero (natural (count + 1)) := by
  rw [← ofRat_zero]
  exact (ofRat_lt_iff 0 ((count + 1 : Nat) : Rat)).mpr (Rat.natCast_pos.mpr (Nat.succ_pos count))

private theorem power_one : ∀ count : Nat, power one count = one
  | 0 => rfl
  | count + 1 => by rw [power_succ, power_one count, one_mul]

private theorem ofReal_one : NNReal.ofReal one = NNReal.one :=
  NNReal.ofReal_toReal NNReal.one

/-- The factorial series at one: `1/n!`. -/
private abbrev reciprocal (count : Nat) : Carrier := factorialTerm one count

private theorem reciprocal_succ (count : Nat) :
    mul (natural (count + 1)) (reciprocal (count + 1)) = reciprocal count := by
  have nonzero : natural (count + 1) ≠ zero := fun vanishing => by
    have positive := natural_succ_positive count
    rw [vanishing] at positive
    exact lt_irrefl zero positive
  show mul (natural (count + 1)) (div (mul one (reciprocal count)) (natural (count + 1))) = _
  rw [one_mul, div_eq_mul_inverse, mul_comm (reciprocal count), ← mul_assoc,
    mul_inverse_cancel nonzero, one_mul]

/-- The step of `choose_factorialTerm`: two coefficients at `n` trials, each
times `1/n!`, add to the coefficient at `n + 1` times `1/(n + 1)!`. -/
private theorem pascal_cancel {first second total left right shifted rest atNext atCount : Carrier}
    (positive : lt zero total) (split : total = add left right)
    (scaled : mul total atNext = atCount)
    (leftStep : mul first atCount = mul (mul left shifted) rest)
    (rightStep : mul second atCount = mul shifted (mul right rest)) :
    mul (add first second) atNext = mul shifted rest := by
  have scaledBoth : mul (mul (add first second) atNext) total = mul (mul shifted rest) total := by
    rw [mul_assoc, mul_comm atNext, scaled, add_mul, leftStep, rightStep, split]
    real_grind
  have nonzero : total ≠ zero := fun vanishing => by
    rw [vanishing] at positive
    exact lt_irrefl zero positive
  have cancelled := congrArg (fun value => mul value (inverse total)) scaledBoth
  simp only [mul_assoc, mul_inverse_cancel nonzero, mul_one] at cancelled
  exact cancelled

/-- The coefficient through the factorial series:
`C(n, k) (1/n!) = (1/k!) (1/(n - k)!)` at `k ≤ n`. -/
public theorem choose_factorialTerm : ∀ {count chosen : Nat}, chosen ≤ count →
    mul (selection.ofRat ((choose count chosen : Nat) : Rat)) (factorialTerm one count) =
      mul (factorialTerm one chosen) (factorialTerm one (count - chosen))
  | count, 0, _ => by
      rw [choose_zero_right, Nat.sub_zero]
      show mul (natural 1) _ = mul one _
      rw [natural_one]
  | 0, _ + 1, below => absurd below (Nat.not_succ_le_zero _)
  | count + 1, chosen + 1, below => by
      have earlier : chosen ≤ count := Nat.le_of_succ_le_succ below
      have first := choose_factorialTerm earlier
      have scaled := reciprocal_succ count
      have shifted := reciprocal_succ chosen
      rw [Nat.succ_sub_succ]
      rcases Nat.lt_or_ge chosen count with inside | edge
      · have second := choose_factorialTerm (Nat.succ_le_of_lt inside)
        have rest := reciprocal_succ (count - (chosen + 1))
        rw [show count - (chosen + 1) + 1 = count - chosen by omega] at rest
        change mul (natural (choose count chosen + choose count (chosen + 1))) (reciprocal (count + 1)) =
          mul (reciprocal (chosen + 1)) (reciprocal (count - chosen))
        change mul (natural (choose count chosen)) (reciprocal count) =
          mul (reciprocal chosen) (reciprocal (count - chosen)) at first
        change mul (natural (choose count (chosen + 1))) (reciprocal count) =
          mul (reciprocal (chosen + 1)) (reciprocal (count - (chosen + 1))) at second
        have total : natural (count + 1) =
            add (natural (chosen + 1)) (natural (count - chosen)) := by
          rw [← natural_add]
          exact congrArg natural (by omega)
        rw [← shifted] at first
        rw [← rest] at second
        rw [natural_add]
        exact pascal_cancel (natural_succ_positive count) total scaled first second
      · have same : chosen = count := Nat.le_antisymm earlier edge
        subst same
        rw [choose_self, Nat.sub_self]
        show mul (natural 1) (reciprocal (chosen + 1)) = mul (reciprocal (chosen + 1)) one
        rw [natural_one, one_mul, mul_one]

/-! ### The masses -/

/-- The binomial mass as a real, `C(n, k) p^k (1 - p)^(n - k)`. Past `n` the
coefficient is zero. -/
@[expose] public def term (count : Nat) (success : Carrier) (successes : Nat) : Carrier :=
  mul (selection.ofRat ((choose count successes : Nat) : Rat))
    (mul (power success successes) (power (sub one success) (count - successes)))

/-- The binomial mass. -/
@[expose] public def mass (count : Nat) (success : Carrier) (successes : Nat) : NNReal :=
  NNReal.ofReal (term count success successes)

public theorem term_of_lt {count successes : Nat} (success : Carrier) (less : count < successes) :
    term count success successes = zero := by
  rw [term, choose_of_lt less]
  show mul (natural 0) _ = zero
  rw [natural_zero, zero_mul]

public theorem term_nonnegative {success : Carrier} (lower : le zero success)
    (upper : le success one) (count successes : Nat) :
    le zero (term count success successes) :=
  mul_nonnegative (natural_nonnegative _)
    (mul_nonnegative (power_nonnegative lower _) (power_nonnegative (sub_nonnegative upper) _))

/-- With no successes, every trial fails. -/
public theorem term_succ_zero (count : Nat) (success : Carrier) :
    term (count + 1) success 0 = mul (sub one success) (term count success 0) := by
  simp only [term, choose_zero_right, Nat.sub_zero, power_zero, power_succ]
  real_grind

/-- Pascal's rule on masses: `k + 1` successes in `n + 1` trials end in a
success after `k` or in a failure after `k + 1`. -/
public theorem term_succ (count successes : Nat) (success : Carrier) :
    term (count + 1) success (successes + 1) =
      add (mul success (term count success successes))
        (mul (sub one success) (term count success (successes + 1))) := by
  rcases Nat.lt_or_ge successes count with inside | outside
  · simp only [term, choose_succ_succ]
    rw [Nat.succ_sub_succ, show count - successes = (count - (successes + 1)) + 1 by omega]
    simp only [power_succ]
    change mul (natural (choose count successes + choose count (successes + 1))) _ = _
    rw [natural_add]
    real_grind
  · rcases Nat.eq_or_lt_of_le outside with same | beyond
    · subst same
      rw [term_of_lt success (Nat.lt_succ_self _), mul_zero, add_zero]
      simp only [term, choose_self, Nat.sub_self, power_zero, power_succ]
      real_grind
    · rw [term_of_lt success (Nat.succ_lt_succ beyond), term_of_lt success beyond,
        term_of_lt success (Nat.lt_succ_of_lt beyond), mul_zero, mul_zero, add_zero]

/-- The partial sums at `n + 1` trials are the partial sums at `n` trials after
a success and after a failure. -/
private theorem partial_succ (count : Nat) (success : Carrier) : ∀ cutoff : Nat,
    partialSum (term (count + 1) success) (cutoff + 1) =
      add (mul success (partialSum (term count success) cutoff))
        (mul (sub one success) (partialSum (term count success) (cutoff + 1)))
  | 0 => by
      simp only [partialSum, term_succ_zero]
      real_grind
  | cutoff + 1 => by
      have before := partial_succ count success cutoff
      rw [partialSum_succ (term (count + 1) success) (cutoff + 1), before, term_succ]
      simp only [partialSum_succ]
      real_grind

/-- The binomial theorem: the masses through `n` sum to `(p + (1 - p))^n = 1`,
at every real `p`. -/
public theorem term_sum (success : Carrier) : ∀ count : Nat,
    partialSum (term count success) (count + 1) = one
  | 0 => by
      show add zero (term 0 success 0) = one
      simp only [term, choose_zero_right, power_zero]
      show add zero (mul (natural 1) (mul one one)) = one
      rw [natural_one]
      real_grind
  | count + 1 => by
      rw [partial_succ, term_sum success count, partialSum_succ, term_of_lt success
        (Nat.lt_succ_self count), term_sum success count]
      real_grind

/-! ### The law -/

/-- The binomial law: `k` successes have mass `C(n, k) p^k (1 - p)^(n - k)`. -/
@[expose] public def law (count : Nat) (success : Carrier) : Measure (Space.discrete Nat) :=
  ofMass (mass count success)

public theorem law_singleton (count : Nat) (success : Carrier) (successes : Nat) :
    law count success (fun value => value = successes) =
      ENNReal.finite (mass count success successes) :=
  ofMass_singleton _ successes

/-- Partial sums that are constant past a stage converge to that constant. -/
private theorem converges_of_eventually {values : Nat → Carrier} {limit : Carrier} {stage : Nat}
    (constant : ∀ index, stage ≤ index → values index = limit) :
    Problib.Analysis.Real.ConvergesTo values limit := fun epsilon positive =>
  ⟨stage, fun index later => by
    rw [constant index later, sub_self, Problib.Analysis.Real.abs_zero]
    exact positive⟩

/-- On `0 ≤ p ≤ 1` the binomial law is a probability measure. -/
public theorem law_isProbability {success : Carrier} (lower : le zero success)
    (upper : le success one) (count : Nat) : Measure.IsProbability (law count success) :=
  ofMass_isProbability (term_nonnegative lower upper count)
    (converges_of_eventually (stage := count + 1) fun _ later =>
      (partialSum_zero_after (fun _ beyond => term_of_lt success (Nat.lt_of_succ_le beyond))
        later).trans (term_sum success count))

/-- The binomial law at a mass function that is the unit at one count is the
point mass there. -/
private theorem law_eq_dirac {count : Nat} {success : Carrier} (point : Nat)
    (masses : ∀ successes, mass count success successes =
      if successes = point then NNReal.one else NNReal.zero) :
    law count success = Measure.dirac _ point := by
  apply ext_singleton
  intro successes
  rw [law_singleton, masses]
  by_cases same : successes = point
  · rw [ite_eq_left same, Measure.dirac_apply_of_mem (Space.discrete Nat) point
      (set := fun value => value = successes) (Space.discrete_measurable _) same.symm]
    rfl
  · rw [ite_eq_right same, Measure.dirac_apply_of_not_mem (Space.discrete Nat) point
      (set := fun value => value = successes) (Space.discrete_measurable _)
      (fun equal => same equal.symm)]
    rfl

/-- With no trials there are no successes. -/
public theorem law_count_zero (success : Carrier) : law 0 success = Measure.dirac _ 0 := by
  apply law_eq_dirac
  intro successes
  cases successes with
  | zero =>
      rw [ite_eq_left (rfl : (0 : Nat) = 0), mass]
      simp only [term, choose_zero_right, power_zero]
      show NNReal.ofReal (mul (natural 1) (mul one one)) = NNReal.one
      rw [natural_one, mul_one, mul_one]
      exact ofReal_one
  | succ successes =>
      rw [ite_eq_right (Nat.succ_ne_zero _), mass, term_of_lt success (Nat.succ_pos _)]
      exact NNReal.ofReal_zero

/-- Trials that never succeed give no successes. -/
public theorem law_zero (count : Nat) : law count zero = Measure.dirac _ 0 := by
  apply law_eq_dirac
  intro successes
  cases successes with
  | zero =>
      rw [ite_eq_left (rfl : (0 : Nat) = 0), mass]
      simp only [term, choose_zero_right, power_zero, Nat.sub_zero, sub_zero]
      show NNReal.ofReal (mul (natural 1) (mul one (power one count))) = NNReal.one
      rw [natural_one, power_one, mul_one, mul_one]
      exact ofReal_one
  | succ successes =>
      rw [ite_eq_right (Nat.succ_ne_zero _), mass, term, power_succ, zero_mul, zero_mul, mul_zero]
      exact NNReal.ofReal_zero

/-- Trials that always succeed give exactly `n` successes. -/
public theorem term_one_of_ne {count successes : Nat} (different : successes ≠ count) :
    term count one successes = zero := by
  rcases Nat.lt_or_gt_of_ne different with below | above
  · rw [term, sub_self, show count - successes = (count - successes - 1) + 1 by omega, power_succ,
      zero_mul, mul_zero, mul_zero]
  · exact term_of_lt one above

/-- Trials that always succeed give `n` successes. -/
public theorem law_one (count : Nat) : law count one = Measure.dirac _ count := by
  apply law_eq_dirac
  intro successes
  by_cases same : successes = count
  · subst same
    rw [ite_eq_left rfl, mass, term, choose_self, Nat.sub_self, power_zero, power_one]
    show NNReal.ofReal (mul (natural 1) (mul one one)) = NNReal.one
    rw [natural_one, mul_one, mul_one]
    exact ofReal_one
  · rw [ite_eq_right same, mass, term_one_of_ne same]
    exact NNReal.ofReal_zero

/-! ### The support and the logarithm -/

/-- Where the term is positive the successes are within the trials, and each
power with a positive exponent has a positive base. -/
public theorem term_support {success : Carrier} (lower : le zero success) (upper : le success one)
    {count successes : Nat} (positive : lt zero (term count success successes)) :
    successes ≤ count ∧ (0 < successes → lt zero success) ∧
      (0 < count - successes → lt zero (sub one success)) := by
  refine ⟨Nat.le_of_not_lt fun above => ?_, fun some => ?_, fun some => ?_⟩
  · rw [term_of_lt success above] at positive
    exact lt_irrefl zero positive
  · refine Classical.byContradiction fun outside => ?_
    have origin : success = zero := le_antisymm (not_lt_iff_le.mp outside) lower
    rw [term, origin, show successes = (successes - 1) + 1 by omega, power_succ, zero_mul,
      zero_mul, mul_zero] at positive
    exact lt_irrefl zero positive
  · refine Classical.byContradiction fun outside => ?_
    have origin : sub one success = zero :=
      le_antisymm (not_lt_iff_le.mp outside) (sub_nonnegative upper)
    rw [term, origin, show count - successes = (count - successes - 1) + 1 by omega, power_succ,
      zero_mul, mul_zero, mul_zero] at positive
    exact lt_irrefl zero positive

/-- Within the trials the coefficient is a quotient of reciprocal factorials,
`n! / (k! (n - k)!)`. -/
public theorem choose_eq_div {count chosen : Nat} (within : chosen ≤ count) :
    selection.ofRat ((choose count chosen : Nat) : Rat) =
      div (mul (factorialTerm one chosen) (factorialTerm one (count - chosen)))
        (factorialTerm one count) := by
  have nonzero : factorialTerm one count ≠ zero := fun vanishes =>
    lt_irrefl zero (vanishes ▸ factorialTerm_one_positive count)
  rw [← choose_factorialTerm within, div_eq_mul_inverse, mul_assoc, mul_inverse_cancel nonzero,
    mul_one]

/-- A power of a positive base is positive. -/
public theorem power_positive {base : Carrier} (positive : lt zero base) : ∀ count : Nat,
    lt zero (power base count)
  | 0 => by rw [power_zero]; exact one_positive
  | count + 1 => by rw [power_succ]; exact mul_positive positive (power_positive positive count)

/-- `log (b^k) = k log b` at a positive base. -/
public theorem log_power {base : Carrier} (positive : lt zero base) (count : Nat) :
    logIntegral (power base count) = mul (selection.ofRat (count : Rat)) (logIntegral base) := by
  rw [← Problib.Analysis.rpow_nat positive.1, Problib.Analysis.rpow_of_positive positive,
    Problib.Analysis.log_exp]

/-! ### Measurability -/

/-- Each power is Borel measurable. -/
public theorem power_measurable : ∀ count : Nat,
    MeasurableMap borel borel (fun value : Carrier => power value count)
  | 0 => MeasurableMap.constant borel borel one
  | count + 1 => MeasurableMap.comp Problib.Measure.Real.mul_measurable
      (Space.pair_measurable (MeasurableMap.identity borel) (power_measurable count))

/-- At fixed counts the mass is measurable in the success probability. -/
public theorem term_measurable (count successes : Nat) :
    MeasurableMap borel borel (fun success => term count success successes) :=
  MeasurableMap.comp Problib.Measure.Real.mul_measurable
    (Space.pair_measurable (MeasurableMap.constant borel borel _)
      (MeasurableMap.comp Problib.Measure.Real.mul_measurable
        (Space.pair_measurable (power_measurable successes)
          (MeasurableMap.comp (power_measurable (count - successes))
            (MeasurableMap.comp Problib.Measure.Real.sub_measurable
              (Space.pair_measurable (MeasurableMap.constant borel borel one)
                (MeasurableMap.identity borel)))))))

end

end Problib.Analysis.Count.Binomial
