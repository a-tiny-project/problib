module

public import Problib.Analysis.Count.Binomial
public import Problib.Measure.Kernel.Composition.Bind
public import Problib.Measure.Kernel.Product.Finite
public import Problib.Measure.Integral.Density.Change
public import Problib.Countable.Bijection
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Space.Countable

/-! The multinomial law on counts over `K` categories.

`n` independent draws from the categorical law `p` give the counts `x` with
probability `n!/(x₀! ⋯ x_{K-1}!) p₀^x₀ ⋯ p_{K-1}^x_{K-1}` when the counts total
`n`, and zero otherwise (`law_singleton`). The coefficient is a product of
binomial coefficients, `C(n, x₀)` times the coefficient of the remaining counts
(`coefficient`), and it meets the factorial series through
`coefficient x · (1/n!) = Π (1/xᵢ!)` (`coefficient_factorialTerm`).

The law is the density of that mass against counting on each coordinate
(`counting`), the reference split at coordinate zero.

The same law is a chain of binomial draws (`chain_eq_law`). Over weights `w`,
count zero is binomial in `n` trials at `w₀ / Σw`, and the remaining counts are
the chain at the remaining trials and the remaining weights. A sampler that
draws the `K - 1` conditional binomials cites this theorem. The chain reads its
weights unnormalized, and division by a zero total is zero, so it holds at
positive total and, trivially, at zero trials.
-/

set_option autoImplicit false

namespace Problib.Analysis.Count.Multinomial

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm power power_zero power_succ power_add
  power_nonnegative factorialTerm_one_positive)
open Problib.Analysis.Logarithm (logIntegral)

noncomputable section

/-! ### Sums and products over the categories -/

/-- The categories after the first. -/
@[expose] public def tail {α : Type} {count : Nat} (values : Fin (count + 1) → α) : Fin count → α :=
  fun index => values index.succ

/-- The total of the counts. -/
@[expose] public def total : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, counts => counts 0 + total count (tail counts)

/-- The total of real weights. -/
@[expose] public def weightTotal : (count : Nat) → (Fin count → Carrier) → Carrier
  | 0, _ => zero
  | count + 1, weights => add (weights 0) (weightTotal count (tail weights))

/-- The product of reals over the categories. -/
@[expose] public def product : (count : Nat) → (Fin count → Carrier) → Carrier
  | 0, _ => one
  | count + 1, values => mul (values 0) (product count (tail values))

/-- The multinomial coefficient `n!/(x₀! ⋯ x_{K-1}!)`, as `C(n, x₀)` times the
coefficient of the remaining counts. -/
@[expose] public def coefficient : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 1
  | count + 1, counts =>
      Binomial.choose (total (count + 1) counts) (counts 0) * coefficient count (tail counts)

/-- A natural number as a real. -/
private abbrev natural (count : Nat) : Carrier := selection.ofRat (count : Rat)

private theorem natural_mul (first second : Nat) :
    natural (first * second) = mul (natural first) (natural second) := by
  show selection.ofRat ((first * second : Nat) : Rat) = _
  rw [Rat.natCast_mul, ofRat_mul]

private theorem natural_one : natural 1 = one := ofRat_one

private theorem natural_zero : natural 0 = zero := ofRat_zero

private theorem power_one : ∀ count : Nat, power one count = one
  | 0 => rfl
  | count + 1 => by rw [power_succ, power_one count, one_mul]

private theorem ofReal_one : NNReal.ofReal one = NNReal.one :=
  NNReal.ofReal_toReal NNReal.one

private theorem natural_nonnegative (count : Nat) : le zero (natural count) := by
  rw [← ofRat_zero]
  exact (ofRat_le_iff 0 (count : Rat)).mpr Rat.natCast_nonneg

public theorem product_nonnegative : ∀ {count : Nat} {values : Fin count → Carrier},
    (∀ index, le zero (values index)) → le zero (product count values)
  | 0, _, _ => one_nonnegative
  | _ + 1, _, nonnegative =>
      mul_nonnegative (nonnegative 0) (product_nonnegative fun index => nonnegative index.succ)

/-- The coefficient through the factorial series:
`coefficient x · (1/n!) = Π (1/xᵢ!)`, `n` the total of `x`. -/
public theorem coefficient_factorialTerm : ∀ (count : Nat) (counts : Fin count → Nat),
    mul (selection.ofRat ((coefficient count counts : Nat) : Rat))
        (factorialTerm one (total count counts)) =
      product count (fun index => factorialTerm one (counts index))
  | 0, _ => by
      show mul (natural 1) one = one
      rw [natural_one, mul_one]
  | count + 1, counts => by
      have rest := coefficient_factorialTerm count (tail counts)
      have head := Binomial.choose_factorialTerm (Nat.le_add_right (counts 0) (total count (tail counts)))
      rw [Nat.add_sub_cancel_left] at head
      change mul (natural (Binomial.choose (counts 0 + total count (tail counts)) (counts 0) *
          coefficient count (tail counts))) (factorialTerm one (counts 0 + total count (tail counts))) =
        mul (factorialTerm one (counts 0)) (product count (tail fun index => factorialTerm one (counts index)))
      change mul (natural (Binomial.choose (counts 0 + total count (tail counts)) (counts 0)))
        (factorialTerm one (counts 0 + total count (tail counts))) =
          mul (factorialTerm one (counts 0)) (factorialTerm one (total count (tail counts))) at head
      change mul (natural (coefficient count (tail counts))) (factorialTerm one (total count (tail counts))) =
        product count (tail fun index => factorialTerm one (counts index)) at rest
      rw [natural_mul, ← rest]
      real_grind

/-- A constant raised to each count multiplies to the constant raised to the
total. -/
public theorem product_power_constant (base : Carrier) : ∀ (count : Nat) (counts : Fin count → Nat),
    product count (fun index => power base (counts index)) = power base (total count counts)
  | 0, _ => rfl
  | count + 1, counts => by
      show mul (power base (counts 0)) (product count (tail fun index => power base (counts index))) = _
      rw [show (tail fun index => power base (counts index)) =
          (fun index => power base (tail counts index)) from rfl,
        product_power_constant base count (tail counts), ← power_add]
      rfl

private theorem power_mul (left right : Carrier) : ∀ count : Nat,
    power (mul left right) count = mul (power left count) (power right count)
  | 0 => by rw [power_zero, power_zero, power_zero, mul_one]
  | count + 1 => by
      rw [power_succ, power_succ, power_succ, power_mul left right count]
      real_grind

/-- Scaling every base by one factor scales the product by that factor raised
to the total. -/
public theorem product_power_scale (factor : Carrier) : ∀ (count : Nat) (bases : Fin count → Carrier)
    (counts : Fin count → Nat),
    product count (fun index => power (mul factor (bases index)) (counts index)) =
      mul (power factor (total count counts)) (product count fun index => power (bases index) (counts index))
  | 0, _, _ => by
      show one = mul one one
      rw [mul_one]
  | count + 1, bases, counts => by
      show mul (power (mul factor (bases 0)) (counts 0))
          (product count fun index => power (mul factor (tail bases index)) (tail counts index)) =
        mul (power factor (counts 0 + total count (tail counts)))
          (mul (power (bases 0) (counts 0))
            (product count fun index => power (tail bases index) (tail counts index)))
      rw [product_power_scale factor count (tail bases) (tail counts), power_mul, power_add]
      real_grind

/-- Nonnegative weights have a nonnegative total. -/
public theorem weightTotal_nonnegative : ∀ {count : Nat} {weights : Fin count → Carrier},
    (∀ index, le zero (weights index)) → le zero (weightTotal count weights)
  | 0, _, _ => le_refl zero
  | _ + 1, _, nonnegative =>
      add_nonnegative (nonnegative 0) (weightTotal_nonnegative fun index => nonnegative index.succ)

/-- Nonnegative weights of zero total are all zero. -/
public theorem weights_zero : ∀ {count : Nat} {weights : Fin count → Carrier},
    (∀ index, le zero (weights index)) → weightTotal count weights = zero →
      ∀ index, weights index = zero
  | 0, _, _, _, index => index.elim0
  | count + 1, weights, nonnegative, vanishing, index => by
      have rest : le zero (weightTotal count (tail weights)) := weightTotal_nonnegative
        fun index => nonnegative index.succ
      have head := nonnegative 0
      change add (weights 0) (weightTotal count (tail weights)) = zero at vanishing
      have first : weights 0 = zero := by real_grind
      have others : weightTotal count (tail weights) = zero := by real_grind
      refine Fin.cases first (fun position => ?_) index
      exact weights_zero (fun index => nonnegative index.succ) others position

/-! ### The masses -/

/-- The multinomial mass as a real: the coefficient times `Π pᵢ^xᵢ` where the
counts total `n`, and zero elsewhere. -/
@[expose] public def term {count : Nat} (trials : Nat) (probabilities : Fin count → Carrier)
    (counts : Fin count → Nat) : Carrier := by
  classical
  exact if total count counts = trials then
    mul (selection.ofRat ((coefficient count counts : Nat) : Rat))
      (product count fun index => power (probabilities index) (counts index))
  else zero

/-- The multinomial mass. -/
@[expose] public def mass {count : Nat} (trials : Nat) (probabilities : Fin count → Carrier)
    (counts : Fin count → Nat) : NNReal :=
  NNReal.ofReal (term trials probabilities counts)

/-- The categorical probabilities of weights: each over their total. -/
@[expose] public def normalize {count : Nat} (weights : Fin count → Carrier) : Fin count → Carrier :=
  fun index => div (weights index) (weightTotal count weights)

/-- The remaining categories read against all the weights are the remaining
categories read against their own weights, scaled by the share the first category
leaves. -/
private theorem tail_scale {count : Nat} (weights : Fin (count + 2) → Carrier)
    (nonnegative : ∀ index, le zero (weights index)) (counts : Fin (count + 1) → Nat) :
    (product (count + 1) fun index => power (normalize weights index.succ) (counts index)) =
      mul (power (sub one (normalize weights 0)) (total (count + 1) counts))
        (product (count + 1) fun index => power (normalize (tail weights) index) (counts index)) := by
  have split : weightTotal (count + 2) weights =
      add (weights 0) (weightTotal (count + 1) (tail weights)) := rfl
  have rest : le zero (weightTotal (count + 1) (tail weights)) :=
    weightTotal_nonnegative fun index => nonnegative index.succ
  have head := nonnegative 0
  by_cases vanishing : weightTotal (count + 1) (tail weights) = zero
  · have each := weights_zero (fun index => nonnegative index.succ) vanishing
    have reads : ∀ index : Fin (count + 1), normalize weights index.succ = zero := fun index => by
      show div (weights index.succ) _ = zero
      rw [show weights index.succ = zero from each index]
      real_grind
    have own : ∀ index : Fin (count + 1), normalize (tail weights) index = zero := fun index => by
      show div (weights index.succ) _ = zero
      rw [each index]
      real_grind
    simp only [reads, own]
    rw [product_power_constant]
    cases total (count + 1) counts with
    | zero => rw [power_zero, power_zero, mul_one]
    | succ total => rw [power_succ, power_succ, zero_mul, mul_zero]
  · have share : sub one (normalize weights 0) =
        div (weightTotal (count + 1) (tail weights)) (weightTotal (count + 2) weights) := by
      show sub one (div (weights 0) (weightTotal (count + 2) weights)) = _
      rw [split]
      have positive : lt zero (weightTotal (count + 1) (tail weights)) := by real_grind
      real_grind
    have reads : ∀ index : Fin (count + 1), normalize weights index.succ =
        mul (div (weightTotal (count + 1) (tail weights)) (weightTotal (count + 2) weights))
          (normalize (tail weights) index) := fun index => by
      show div (weights index.succ) _ = mul _ (div (tail weights index) _)
      show _ = mul _ (div (weights index.succ) _)
      real_grind
    simp only [reads]
    rw [product_power_scale, share]

/-- The mass splits at category zero into a binomial mass and the mass of the
remaining counts at the remaining trials and the remaining weights. It holds at
every nonnegative weights, the zero total included, because both sides read
division by zero as zero. -/
public theorem term_split {count : Nat} (trials : Nat) (weights : Fin (count + 2) → Carrier)
    (nonnegative : ∀ index, le zero (weights index)) (counts : Fin (count + 2) → Nat) :
    term trials (normalize weights) counts =
      mul (Binomial.term trials (normalize weights 0) (counts 0))
        (term (trials - counts 0) (normalize (tail weights)) (tail counts)) := by
  classical
  have totalSplit : total (count + 2) counts = counts 0 + total (count + 1) (tail counts) := rfl
  by_cases reaches : total (count + 2) counts = trials
  · have rest : total (count + 1) (tail counts) = trials - counts 0 := by omega
    have below : counts 0 ≤ trials := by omega
    rw [term, term, ite_eq_left reaches, ite_eq_left rest, Binomial.term]
    have scaled := tail_scale weights nonnegative (tail counts)
    rw [rest] at scaled
    change mul (natural (Binomial.choose (total (count + 2) counts) (counts 0) *
        coefficient (count + 1) (tail counts)))
      (mul (power (normalize weights 0) (counts 0))
        (product (count + 1) fun index => power (normalize weights index.succ) (tail counts index))) = _
    rw [scaled, reaches, natural_mul]
    real_grind
  · rw [term, ite_eq_right reaches]
    rcases Nat.lt_or_ge trials (counts 0) with above | below
    · rw [Binomial.term_of_lt _ above, zero_mul]
    · have rest : total (count + 1) (tail counts) ≠ trials - counts 0 := by omega
      rw [term, ite_eq_right rest, mul_zero]

/-! ### The reference -/

/-- Counts over `count` categories, each a discrete natural. -/
public abbrev space (count : Nat) : Space (Fin count → Nat) :=
  Space.pi fun _ : Fin count => Space.discrete Nat

private theorem cases_tail {count : Nat} (counts : Fin (count + 1) → Nat) :
    (Fin.cases (counts 0) (tail counts) : Fin (count + 1) → Nat) = counts :=
  funext fun index => Fin.cases rfl (fun _ => rfl) index

private theorem cases_eq_iff {count : Nat} (head : Nat) (rest : Fin count → Nat)
    (counts : Fin (count + 1) → Nat) :
    (Fin.cases head rest : Fin (count + 1) → Nat) = counts ↔ head = counts 0 ∧ rest = tail counts := by
  constructor
  · intro equal
    subst equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact cases_tail counts

/-- Every set of counts is measurable one point at a time. -/
public theorem singleton_measurable : ∀ {count : Nat} (counts : Fin count → Nat),
    (space count).Measurable (Set.singleton counts)
  | 0, counts => by
      have every : Set.singleton counts = Set.univ :=
        Set.ext fun other => ⟨fun _ => True.intro, fun _ => funext fun index => index.elim0⟩
      rw [every]
      exact Space.univ _
  | count + 1, counts => by
      have split : MeasurableMap (space (count + 1)) (Space.product (Space.discrete Nat) (space count))
          (fun values => (values 0, tail values)) :=
        Space.pair_measurable (Space.coordinate_measurable (fun _ : Fin (count + 1) => Space.discrete Nat) 0)
          (Space.pi_measurable fun (index : Fin count) =>
            Space.coordinate_measurable (fun _ : Fin (count + 1) => Space.discrete Nat) index.succ)
      have same : Set.singleton counts = Set.preimage (fun values => (values 0, tail values))
          (Set.product (Set.singleton (counts 0)) (Set.singleton (tail counts))) := by
        apply Set.ext
        intro values
        show values = counts ↔ values 0 = counts 0 ∧ tail values = tail counts
        rw [← cases_eq_iff (values 0) (tail values) counts, cases_tail]
      rw [same]
      exact split (Space.product_set_measurable _ _ (Space.discrete_measurable _)
        (singleton_measurable (tail counts)))

/-- Two measures on counts agreeing at every point are equal. -/
public theorem ext_singleton {count : Nat} {left right : Measure (space count)}
    (same : ∀ counts, left (Set.singleton counts) = right (Set.singleton counts)) : left = right :=
  Measure.ext_of_atoms (Problib.Countable.Pair.encodeTuple count)
    (Problib.Countable.Pair.encodeTuple_injective count) singleton_measurable same

/-- A count at category zero and the counts of the later categories. -/
@[expose] public def cons {count : Nat} (pair : Nat × (Fin count → Nat)) : Fin (count + 1) → Nat :=
  Fin.cases pair.1 pair.2

public theorem cons_pair_measurable (count : Nat) :
    MeasurableMap (Space.product (Space.discrete Nat) (space count)) (space (count + 1)) cons :=
  Kernel.cons_measurable (Space.discrete Nat) count

/-- Counting on each coordinate, with its s-finite presentation: the unit
mass on no categories, and a product with counting at coordinate zero. -/
@[expose] public def reference : (count : Nat) → (measure : Measure (space count)) × Measure.SFinite measure
  | 0 => ⟨Measure.dirac _ (fun index => index.elim0),
      Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)⟩
  | count + 1 =>
      ⟨(Measure.prod Measure.counting (reference count).1 (reference count).2).map cons
          (cons_pair_measurable count),
        (Measure.countingSigmaFinite.toSFinite.prod (reference count).2).map cons
          (cons_pair_measurable count)⟩

/-- Counting on each coordinate. -/
@[expose] public def counting (count : Nat) : Measure (space count) := (reference count).1

public theorem counting_succ (count : Nat) :
    counting (count + 1) =
      (Measure.prod Measure.counting (reference count).1 (reference count).2).map cons
      (cons_pair_measurable count) := rfl

/-- Counting gives each point unit mass. -/
public theorem counting_singleton : ∀ {count : Nat} (counts : Fin count → Nat),
    counting count (Set.singleton counts) = ENNReal.one
  | 0, counts => Measure.dirac_apply_of_mem (space 0) (fun index => index.elim0)
      (singleton_measurable counts) (funext fun index => index.elim0)
  | count + 1, counts => by
      have same : Set.preimage cons (Set.singleton counts) =
          Set.product (Set.singleton (counts 0)) (Set.singleton (tail counts)) :=
        Set.ext fun pair => cases_eq_iff pair.1 pair.2 counts
      rw [counting_succ, Measure.map_apply _ _ _ (singleton_measurable counts), same,
        Measure.prod_apply_product _ _ _ (Space.discrete_measurable _) (singleton_measurable _),
        show Measure.counting (Set.singleton (counts 0)) = ENNReal.one from
          Measure.counting_singleton (counts 0)]
      exact (ENNReal.one_mul _).trans (counting_singleton (tail counts))

/-! ### The law -/

/-- The multinomial law: the counts `x` have the multinomial mass. -/
@[expose] public def law {count : Nat} (trials : Nat) (probabilities : Fin count → Carrier) :
    Measure (space count) :=
  (counting count).withDensity fun counts => ENNReal.finite (mass trials probabilities counts)

/-- The density against a reference that gives each point unit mass is the
point's mass. -/
private theorem withDensity_singleton {count : Nat} (density : (Fin count → Nat) → ENNReal)
    (counts : Fin count → Nat) :
    (counting count).withDensity density (Set.singleton counts) = density counts := by
  rw [Measure.withDensity_apply _ _ (singleton_measurable counts),
    ← lintegral_indicator _ _ (singleton_measurable counts)]
  have same : ennrealIndicator (Set.singleton counts) density =
      ennrealIndicator (Set.singleton counts) fun _ => density counts := by
    funext other
    by_cases at_point : other = counts
    · rw [ennrealIndicator_of_mem (region := Set.singleton counts) at_point,
        ennrealIndicator_of_mem (region := Set.singleton counts) at_point, at_point]
    · rw [ennrealIndicator_of_not_mem (region := Set.singleton counts) at_point,
        ennrealIndicator_of_not_mem (region := Set.singleton counts) at_point]
  rw [same, lintegral_indicator _ _ (singleton_measurable counts), lintegral_const,
    Measure.restrict_apply_univ, counting_singleton, ENNReal.mul_one]

public theorem law_singleton {count : Nat} (trials : Nat) (probabilities : Fin count → Carrier)
    (counts : Fin count → Nat) :
    law trials probabilities (Set.singleton counts) = ENNReal.finite (mass trials probabilities counts) :=
  withDensity_singleton _ counts

/-! ### The chain of binomials -/

/-- Prepending one count is measurable. -/
public theorem consAt_measurable (count head : Nat) :
    MeasurableMap (space count) (space (count + 1)) (fun rest => cons (head, rest)) :=
  MeasurableMap.comp (cons_pair_measurable count)
    (Space.pair_measurable (MeasurableMap.constant _ _ head) (MeasurableMap.identity _))

/-- The chain of binomials over weights: count zero is binomial in the trials
at `w₀ / Σw`, and the later counts are the chain at the remaining trials and
the later weights. -/
@[expose] public def chain : (count : Nat) → Nat → (Fin (count + 1) → Carrier) →
    Measure (space (count + 1))
  | 0, trials, _ => Measure.dirac _ (fun _ => trials)
  | count + 1, trials, weights =>
      (Binomial.law trials (normalize weights 0)).bind
        ⟨fun head => (chain count (trials - head) (tail weights)).map (fun rest => cons (head, rest))
            (consAt_measurable (count + 1) head),
          fun _ => mass_measurable _⟩

/-- The chain at a point is the binomial mass of its first count times the
chain of the later counts at the remaining trials. -/
public theorem chain_singleton (count trials : Nat) (weights : Fin (count + 2) → Carrier)
    (counts : Fin (count + 2) → Nat) :
    chain (count + 1) trials weights (Set.singleton counts) =
      ENNReal.mul (ENNReal.finite (Binomial.mass trials (normalize weights 0) (counts 0)))
        (chain count (trials - counts 0) (tail weights) (Set.singleton (tail counts))) := by
  have preimage : ∀ head, Set.preimage (fun rest => cons (head, rest)) (Set.singleton counts) =
      if head = counts 0 then Set.singleton (tail counts) else Set.empty := by
    intro head
    apply Set.ext
    intro rest
    show (Fin.cases head rest : Fin (count + 2) → Nat) = counts ↔ _
    rw [cases_eq_iff]
    by_cases same : head = counts 0
    · rw [ite_eq_left same]
      exact ⟨fun both => both.2, fun later => ⟨same, later⟩⟩
    · rw [ite_eq_right same]
      exact ⟨fun both => absurd both.1 same, fun empty => False.elim empty⟩
  rw [chain, Measure.bind_apply _ _ (singleton_measurable counts)]
  show lintegral _ (fun head => ((chain count (trials - head) (tail weights)).map _ _)
    (Set.singleton counts)) = _
  have reads : (fun head => ((chain count (trials - head) (tail weights)).map
        (fun rest => cons (head, rest)) (consAt_measurable (count + 1) head)) (Set.singleton counts)) =
      fun head => chain count (trials - head) (tail weights)
        (Set.preimage (fun rest => cons (head, rest)) (Set.singleton counts)) :=
    funext fun head => Measure.map_apply _ _ _ (singleton_measurable counts)
  rw [reads, Binomial.law, ofMass, lintegral_withDensity _ (mass_measurable _) (mass_measurable _),
    lintegral_counting, ENNReal.tsum_eq_of_at_most_one_nonzero _ (counts 0) fun head different => by
      show ENNReal.mul _ (chain count (trials - head) (tail weights) _) = _
      rw [preimage, ite_eq_right different, Measure.empty_apply, ENNReal.mul_zero]]
  show ENNReal.mul _ (chain count (trials - counts 0) (tail weights) _) = _
  rw [preimage, ite_eq_left rfl]

private theorem normalize_nonnegative {count : Nat} {weights : Fin count → Carrier}
    (nonnegative : ∀ index, le zero (weights index)) (index : Fin count) :
    le zero (normalize weights index) :=
  div_nonnegative (nonnegative index) (weightTotal_nonnegative nonnegative)

private theorem normalize_le_one {count : Nat} {weights : Fin (count + 1) → Carrier}
    (nonnegative : ∀ index, le zero (weights index)) : le (normalize weights 0) one := by
  have rest : le zero (weightTotal count (tail weights)) :=
    weightTotal_nonnegative fun index => nonnegative index.succ
  have head := nonnegative 0
  show le (div (weights 0) (add (weights 0) (weightTotal count (tail weights)))) one
  by_cases vanishing : add (weights 0) (weightTotal count (tail weights)) = zero
  · rw [vanishing, div_eq_mul_inverse, inverse_zero, mul_zero]
    exact one_nonnegative
  · have positive : lt zero (add (weights 0) (weightTotal count (tail weights))) := by real_grind
    have below : le (weights 0) (add (weights 0) (weightTotal count (tail weights))) := by real_grind
    have scaled := mul_le_mul_nonnegative_right below (inverse_nonnegative positive.1)
    rw [mul_inverse_cancel (fun equal => vanishing equal)] at scaled
    rw [div_eq_mul_inverse]
    exact scaled

/-- On nonnegative probabilities every mass is nonnegative. -/
public theorem term_nonnegative {count : Nat} (trials : Nat) {probabilities : Fin count → Carrier}
    (nonnegative : ∀ index, le zero (probabilities index)) (counts : Fin count → Nat) :
    le zero (term trials probabilities counts) := by
  classical
  unfold term
  split
  · exact mul_nonnegative (natural_nonnegative _)
      (product_nonnegative fun index => power_nonnegative (nonnegative index) _)
  · exact le_refl zero

/-- The chain of conditional binomials is the multinomial law of the
normalized weights, at positive total and at zero trials. -/
public theorem chain_eq_law : ∀ (count trials : Nat) (weights : Fin (count + 1) → Carrier),
    (∀ index, le zero (weights index)) →
    (lt zero (weightTotal (count + 1) weights) ∨ trials = 0) →
    chain count trials weights = law trials (normalize weights)
  | 0, trials, weights, nonnegative, reaches => ext_singleton fun counts => by
      classical
      rw [law_singleton]
      show Measure.dirac _ (fun _ => trials) (Set.singleton counts) = _
      rw [Measure.dirac_apply _ _ (singleton_measurable counts)]
      have single : ∀ other : Fin 1 → Nat, other = counts ↔ other 0 = counts 0 := fun other =>
        ⟨fun same => same ▸ rfl, fun same => funext fun index => by
          rw [Subsingleton.elim index 0]; exact same⟩
      by_cases hits : trials = counts 0
      · have point : Set.singleton counts (fun _ : Fin 1 => trials) := (single _).mpr hits
        rw [ite_eq_left point, mass, term, ite_eq_left (show total 1 counts = trials from
          (Nat.add_zero _).trans hits.symm)]
        have base : power (normalize weights 0) (counts 0) = one := by
          rcases reaches with positive | none
          · have whole : normalize weights 0 = one := by
              show div (weights 0) (add (weights 0) zero) = one
              have positive' : lt zero (add (weights 0) zero) := positive
              real_grind
            rw [whole]
            exact power_one _
          · rw [← hits, none, power_zero]
        show ENNReal.one = ENNReal.finite (NNReal.ofReal (mul (natural (Binomial.choose (counts 0 + 0)
          (counts 0) * 1)) (mul (power (normalize weights 0) (counts 0)) one)))
        rw [Nat.add_zero, Nat.mul_one, Binomial.choose_self, natural_one, base, mul_one, mul_one]
        exact (congrArg ENNReal.finite ofReal_one).symm
      · have point : ¬Set.singleton counts (fun _ : Fin 1 => trials) := fun same =>
          hits ((single _).mp same)
        rw [ite_eq_right point, mass, term, ite_eq_right (show total 1 counts ≠ trials from fun same =>
          hits (same.symm.trans (Nat.add_zero _)))]
        exact (congrArg ENNReal.finite NNReal.ofReal_zero).symm
  | count + 1, trials, weights, nonnegative, reaches => ext_singleton fun counts => by
      rw [chain_singleton, law_singleton, mass, term_split trials weights nonnegative counts]
      have binomialNonnegative := Binomial.term_nonnegative (normalize_nonnegative nonnegative 0)
        (normalize_le_one nonnegative) trials (counts 0)
      have laterNonnegative := term_nonnegative (trials - counts 0)
        (probabilities := normalize (tail weights))
        (normalize_nonnegative fun index => nonnegative index.succ) (tail counts)
      by_cases vanishing : Binomial.term trials (normalize weights 0) (counts 0) = zero
      · rw [Binomial.mass, vanishing, zero_mul, NNReal.ofReal_zero]
        exact ENNReal.zero_mul _
      · have laterReaches : lt zero (weightTotal (count + 1) (tail weights)) ∨
            trials - counts 0 = 0 := by
          have rest : le zero (weightTotal (count + 1) (tail weights)) :=
            weightTotal_nonnegative fun index => nonnegative index.succ
          by_cases positive : lt zero (weightTotal (count + 1) (tail weights))
          · exact Or.inl positive
          · right
            have empty : weightTotal (count + 1) (tail weights) = zero := by real_grind
            rcases reaches with whole | none
            · have every : normalize weights 0 = one := by
                show div (weights 0) (add (weights 0) (weightTotal (count + 1) (tail weights))) = one
                change lt zero (add (weights 0) (weightTotal (count + 1) (tail weights))) at whole
                rw [empty] at whole ⊢
                real_grind
              rw [every] at vanishing
              have hits : counts 0 = trials := Classical.byContradiction fun different =>
                vanishing (Binomial.term_one_of_ne different)
              rw [hits, Nat.sub_self]
            · rw [none, Nat.zero_sub]
        rw [chain_eq_law count (trials - counts 0) (tail weights) (fun index => nonnegative index.succ)
          laterReaches, law_singleton, mass, Binomial.mass, ENNReal.finite_mul_finite,
          NNReal.ofReal_mul binomialNonnegative laterNonnegative]

/-- On nonnegative weights the chain is a probability measure. -/
public theorem chain_isProbability : ∀ (count trials : Nat) (weights : Fin (count + 1) → Carrier),
    (∀ index, le zero (weights index)) → Measure.IsProbability (chain count trials weights)
  | 0, _, _, _ => Measure.IsProbability.dirac _ _
  | count + 1, trials, weights, nonnegative =>
      Measure.IsProbability.bind
        (Binomial.law_isProbability (normalize_nonnegative nonnegative 0)
          (normalize_le_one nonnegative) trials) _
        fun head => Measure.IsProbability.map
          (chain_isProbability count (trials - head) (tail weights) fun index => nonnegative index.succ)
          _ (consAt_measurable (count + 1) head)

/-- At positive total the multinomial law of the normalized weights is a
probability measure. -/
public theorem law_isProbability {count : Nat} (trials : Nat) (weights : Fin (count + 1) → Carrier)
    (nonnegative : ∀ index, le zero (weights index))
    (positive : lt zero (weightTotal (count + 1) weights)) :
    Measure.IsProbability (law trials (normalize weights)) := by
  rw [← chain_eq_law count trials weights nonnegative (Or.inl positive)]
  exact chain_isProbability count trials weights nonnegative

/-! ### Folds and logarithms -/

/-- The total is the right fold over the categories in order. -/
public theorem weightTotal_eq_foldr : ∀ (count : Nat) (values : Fin count → Carrier),
    (List.finRange count).foldr (fun index sum => add (values index) sum) zero =
      weightTotal count values
  | 0, _ => rfl
  | count + 1, values => by
      simp only [List.finRange_succ, List.foldr_cons, List.foldr_map]
      exact congrArg (add (values 0)) (weightTotal_eq_foldr count fun index => values index.succ)

/-- The total of `count` ones is `count`. -/
public theorem weightTotal_one : ∀ count : Nat,
    weightTotal count (fun _ => one) = selection.ofRat (count : Rat)
  | 0 => ofRat_zero.symm
  | count + 1 => by
      show add one (weightTotal count fun _ => one) = _
      rw [weightTotal_one count, show ((count + 1 : Nat) : Rat) = (count : Rat) + 1 from
        Rat.natCast_add count 1, ofRat_add, ofRat_one, add_comm]

/-- A product of positives is positive. -/
public theorem product_positive : ∀ (count : Nat) {values : Fin count → Carrier},
    (∀ index, lt zero (values index)) → lt zero (product count values)
  | 0, _, _ => one_positive
  | count + 1, _, positive =>
      mul_positive (positive 0) (product_positive count fun index => positive index.succ)

/-- Negation passes through the total. -/
public theorem weightTotal_neg : ∀ (count : Nat) (values : Fin count → Carrier),
    weightTotal count (fun index => neg (values index)) = neg (weightTotal count values)
  | 0, _ => by
      show zero = neg zero
      real_grind
  | count + 1, values => by
      show add (neg (values 0)) (weightTotal count fun index => neg (values index.succ)) =
        neg (add (values 0) (weightTotal count fun index => values index.succ))
      rw [weightTotal_neg count fun index => values index.succ]
      real_grind

/-- A product with a zero factor is zero. -/
public theorem product_eq_zero : ∀ {count : Nat} {values : Fin count → Carrier} (index : Fin count),
    values index = zero → product count values = zero
  | count + 1, values, index, vanishes => by
      show mul (values 0) (product count fun later => values later.succ) = zero
      cases index using Fin.cases with
      | zero => rw [vanishes, zero_mul]
      | succ later => rw [product_eq_zero (values := fun later => values later.succ) later vanishes, mul_zero]

/-- The logarithm of a product of positives is the total of their logarithms. -/
public theorem log_product : ∀ (count : Nat) {values : Fin count → Carrier},
    (∀ index, lt zero (values index)) →
      logIntegral (product count values) = weightTotal count fun index => logIntegral (values index)
  | 0, _, _ => Problib.Analysis.Logarithm.log_one
  | count + 1, values, positive => by
      show logIntegral (mul (values 0) (product count fun index => values index.succ)) =
        add (logIntegral (values 0)) (weightTotal count fun index => logIntegral (values index.succ))
      rw [Problib.Analysis.Logarithm.log_mul _ _ (positive 0)
        (product_positive count fun index => positive index.succ)]
      exact congrArg _ (log_product count fun index => positive index.succ)

/-- The coefficient's logarithm through reciprocal factorials:
`log (n! / ∏ xᵢ!) = Σ log (1 / xᵢ!) - log (1 / n!)`. -/
public theorem log_coefficient (count : Nat) (counts : Fin count → Nat) :
    logIntegral (selection.ofRat ((coefficient count counts : Nat) : Rat)) =
      sub (weightTotal count fun index => logIntegral (factorialTerm one (counts index)))
        (logIntegral (factorialTerm one (total count counts))) := by
  have factorials : ∀ index, lt zero (factorialTerm one (counts index)) :=
    fun index => factorialTerm_one_positive (counts index)
  have identity := coefficient_factorialTerm count counts
  have coefficientPositive : lt zero (natural (coefficient count counts)) :=
    ⟨natural_nonnegative _, fun below => by
      have vanishes : natural (coefficient count counts) = zero := le_antisymm below (natural_nonnegative _)
      have positive := product_positive count factorials
      rw [← identity] at positive
      change lt zero (mul (natural (coefficient count counts)) _) at positive
      rw [vanishes, zero_mul] at positive
      exact lt_irrefl zero positive⟩
  have logs := congrArg logIntegral identity
  rw [Problib.Analysis.Logarithm.log_mul _ _ coefficientPositive
      (factorialTerm_one_positive (total count counts)), log_product count factorials] at logs
  rw [← logs]
  real_grind

/-! ### Measurability -/

/-- A map into a countable discrete space is measurable when each of its
fibers is. -/
public theorem measurable_of_fibers {α β : Type} {source : Space α} (code : β → Nat)
    (injective : Function.Injective code) {function : α → β}
    (fibers : ∀ value, source.Measurable (fun input => function input = value)) :
    MeasurableMap source (Space.discrete β) function := by
  intro set _
  have equal : Set.preimage function set =
      fun input => ∃ value, (fun input => set value ∧ function input = value) input := by
    apply Set.ext
    intro input
    exact ⟨fun member => ⟨function input, member, rfl⟩,
      fun ⟨_, member, same⟩ => show set (function input) from same ▸ member⟩
  rw [equal]
  refine source.i_union_of_nat_injection code injective _ fun value => ?_
  by_cases member : set value
  · have same : (fun input => set value ∧ function input = value) =
        fun input => function input = value :=
      Set.ext fun _ => ⟨And.right, fun hit => ⟨member, hit⟩⟩
    rw [same]
    exact fibers value
  · have same : (fun input => set value ∧ function input = value) = Set.empty :=
      Set.ext fun _ => ⟨fun hit => member hit.1, False.elim⟩
    rw [same]
    exact source.empty

/-- A total of measurable reals over the categories is measurable. -/
public theorem weightTotal_measurable {α : Type} {source : Space α} :
    ∀ (count : Nat) {values : α → Fin count → Carrier},
      (∀ index, MeasurableMap source borel (fun input => values input index)) →
        MeasurableMap source borel (fun input => weightTotal count (values input))
  | 0, _, _ => MeasurableMap.constant source borel zero
  | count + 1, _, measurable => by
      exact measurable_add (measurable 0)
        (weightTotal_measurable count fun index => measurable index.succ)

/-- A product of measurable reals over the categories is measurable. -/
public theorem product_measurable {α : Type} {source : Space α} :
    ∀ (count : Nat) {values : α → Fin count → Carrier},
      (∀ index, MeasurableMap source borel (fun input => values input index)) →
        MeasurableMap source borel (fun input => product count (values input))
  | 0, _, _ => MeasurableMap.constant source borel one
  | count + 1, _, measurable => by
      exact measurable_mul (measurable 0)
        (product_measurable count fun index => measurable index.succ)

/-- At fixed counts the multinomial term is measurable in the probabilities. -/
public theorem term_measurable {count : Nat} (trials : Nat) (counts : Fin count → Nat) :
    MeasurableMap (Space.pi fun _ : Fin count => borel) borel
      (fun probabilities => term trials probabilities counts) := by
  by_cases reaches : total count counts = trials
  · have same : (fun probabilities : Fin count → Carrier => term trials probabilities counts) =
        fun probabilities => mul (selection.ofRat ((coefficient count counts : Nat) : Rat))
          (product count fun index => power (probabilities index) (counts index)) :=
      funext fun _ => by rw [term, ite_eq_left reaches]
    rw [same]
    exact measurable_mul (MeasurableMap.constant _ borel _)
      (product_measurable count fun index => MeasurableMap.comp
        (Binomial.power_measurable (counts index))
        (Space.coordinate_measurable (fun _ : Fin count => borel) index))
  · have same : (fun probabilities : Fin count → Carrier => term trials probabilities counts) =
        fun _ => zero :=
      funext fun _ => by rw [term, ite_eq_right reaches]
    rw [same]
    exact MeasurableMap.constant _ borel zero

end

end Problib.Analysis.Count.Multinomial
