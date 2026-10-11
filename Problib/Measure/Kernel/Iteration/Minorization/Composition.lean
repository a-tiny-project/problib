module

public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.Kernel.Scale

set_option autoImplicit false

/-! Composition of minorization bounds.

A sampler assembled from several steps needs a minorization of the assembled
step. One-step bounds compose. Throughout, `first.comp second` runs `first` and
then `second`, as `Kernel.comp` does.

- A bound on the step that runs first survives any Markov step after it, with
  the reference pushed through the later step (`minorization_comp_right`,
  `minorization_on_comp_right`).
- A bound on the step that runs second survives any Markov step before it
  (`minorization_comp_left`). From a region that the earlier step enters with
  probability at least `β`, it survives with weight scaled by `β`
  (`minorization_on_of_entrance`).
- A fixed mixture keeps a component's bound scaled by the component's weight
  (`minorization_mixture`), and a block bound over `m` steps scaled by the
  weight's `m`-th power (`minorization_mixture_block`).

A block bound over several steps does not survive interleaving with another
step, so composition takes one-step bounds. -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

public section

/-- A probability law pushed through a Markov kernel. -/
@[expose] noncomputable def lawThrough (law : Giry.Law space)
    (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input)) : Giry.Law space :=
  ⟨law.val.bind kernel, law.property.bind kernel markov⟩

private theorem product_positive {left right : NNReal}
    (leftPositive : NNReal.lt NNReal.zero left)
    (rightPositive : NNReal.lt NNReal.zero right) :
    NNReal.lt NNReal.zero (NNReal.mul left right) := by
  apply (NNReal.zero_lt_iff_ne_zero _).mpr
  intro zero
  rcases NNReal.mul_eq_zero_iff.mp zero with leftZero | rightZero
  · exact (NNReal.zero_lt_iff_ne_zero _).mp leftPositive leftZero
  · exact (NNReal.zero_lt_iff_ne_zero _).mp rightPositive rightZero

private theorem product_at_most_one {left right : NNReal}
    (leftBounded : NNReal.le left NNReal.one)
    (rightBounded : NNReal.le right NNReal.one) :
    NNReal.le (NNReal.mul left right) NNReal.one := by
  have bound := NNReal.mul_le_mul leftBounded rightBounded
  rwa [NNReal.mul_one] at bound

/-- A bound on the step that runs first survives a Markov step after it. The
reference is pushed through the later step. `first.comp second` runs `first`
and then `second`. -/
theorem minorization_on_comp_right {first second : Kernel space space}
    {region : Set α} {weight : NNReal} {reference : Giry.Law space}
    (minor : MinorizationOn first region 1 weight reference)
    (secondMarkov : ∀ input, Measure.IsProbability (second input)) :
    MinorizationOn (first.comp second) region 1 weight
      (lawThrough reference second secondMarkov) where
  markov := fun input => (minor.markov input).bind second secondMarkov
  stepsPositive := Nat.zero_lt_one
  weightPositive := minor.weightPositive
  weightAtMostOne := minor.weightAtMostOne
  lower := by
    intro input inside event eventMeasurable
    have stepMeasurable := second.measurable eventMeasurable
    have bound : ∀ set, space.Measurable set →
        ENNReal.le ((Measure.smul (ENNReal.finite weight) reference.val) set)
          (first input set) := by
      intro set setMeasurable
      have lower := minor.lower input inside set setMeasurable
      rwa [iterate_one] at lower
    rw [iterate_one, comp_apply_measurable _ _ _ eventMeasurable,
      Measure.smul_apply_measurable _ _ eventMeasurable]
    change ENNReal.le (ENNReal.mul (ENNReal.finite weight)
      ((reference.val.bind second) event)) _
    rw [Measure.bind_apply _ _ eventMeasurable,
      ← lintegral_smul_measure]
    exact lintegral_mono_measure _ _ _ bound

/-- A global bound on the step that runs first survives a Markov step after
it. `first.comp second` runs `first` and then `second`. -/
theorem minorization_comp_right {first second : Kernel space space}
    {weight : NNReal} {reference : Giry.Law space}
    (minor : Minorization first 1 weight reference)
    (secondMarkov : ∀ input, Measure.IsProbability (second input)) :
    Minorization (first.comp second) 1 weight
      (lawThrough reference second secondMarkov) :=
  (minorization_on_univ _ _ _ _).mpr
    (minorization_on_comp_right ((minorization_on_univ _ _ _ _).mp minor)
      secondMarkov)

/-- A bound on the step that runs second, from a region, survives a Markov step
before it. From every state of `entrance`, the earlier step enters the region
with probability at least `hit`, so the weight scales by `hit`.
`first.comp second` runs `first` and then `second`. -/
theorem minorization_on_of_entrance {first second : Kernel space space}
    {region entrance : Set α} {weight hit : NNReal} {reference : Giry.Law space}
    (minor : MinorizationOn second region 1 weight reference)
    (regionMeasurable : space.Measurable region)
    (firstMarkov : ∀ input, Measure.IsProbability (first input))
    (hitPositive : NNReal.lt NNReal.zero hit)
    (hitAtMostOne : NNReal.le hit NNReal.one)
    (enters : ∀ input, entrance input →
      ENNReal.le (ENNReal.finite hit) (first input region)) :
    MinorizationOn (first.comp second) entrance 1 (NNReal.mul hit weight)
      reference where
  markov := fun input => (firstMarkov input).bind second minor.markov
  stepsPositive := Nat.zero_lt_one
  weightPositive := product_positive hitPositive minor.weightPositive
  weightAtMostOne := product_at_most_one hitAtMostOne minor.weightAtMostOne
  lower := by
    classical
    intro input inside event eventMeasurable
    let floor := (Measure.smul (ENNReal.finite weight) reference.val) event
    let indicator : α → ENNReal := ennrealIndicator region fun _ => ENNReal.one
    have indicatorMeasurable : ENNRealMeasurable space indicator :=
      ENNRealMeasurable.indicator regionMeasurable (ENNRealMeasurable.constant _ _)
    have pointwise : ∀ state,
        ENNReal.le (ENNReal.mul floor (indicator state)) (second state event) := by
      intro state
      by_cases member : region state
      · have lower := minor.lower state member event eventMeasurable
        rw [iterate_one] at lower
        simp only [indicator, ennrealIndicator, ennrealPiecewise, member, ite_true,
          ENNReal.mul_one]
        exact lower
      · simp only [indicator, ennrealIndicator, ennrealPiecewise, member, ite_false,
          ENNReal.mul_zero]
        exact ENNReal.zero_le _
    have integrated := lintegral_mono (first input) pointwise
    rw [lintegral_smul _ _ indicatorMeasurable,
      ← apply_eq_lintegral_indicator _ regionMeasurable,
      ← comp_apply_measurable _ _ _ eventMeasurable] at integrated
    rw [iterate_one, Measure.smul_apply_measurable _ _ eventMeasurable]
    have scaled : ENNReal.le
        (ENNReal.mul (ENNReal.finite (NNReal.mul hit weight)) (reference.val event))
        (ENNReal.mul floor (first input region)) := by
      have floorValue : floor =
          ENNReal.mul (ENNReal.finite weight) (reference.val event) :=
        Measure.smul_apply_measurable _ _ eventMeasurable
      rw [floorValue, ← ENNReal.finite_mul_finite, ENNReal.mul_assoc,
        ENNReal.mul_comm _ (first input region)]
      exact ENNReal.mul_le_mul (enters input inside) (ENNReal.le_refl _)
    exact ENNReal.le_trans scaled integrated

/-- A global bound on the step that runs second survives a Markov step before
it. `first.comp second` runs `first` and then `second`. -/
theorem minorization_comp_left {first second : Kernel space space}
    {weight : NNReal} {reference : Giry.Law space}
    (minor : Minorization second 1 weight reference)
    (firstMarkov : ∀ input, Measure.IsProbability (first input)) :
    Minorization (first.comp second) 1 weight reference := by
  have entered := minorization_on_of_entrance
    ((minorization_on_univ _ _ _ _).mp minor) space.univ firstMarkov
    (hitPositive := (NNReal.zero_lt_iff_ne_zero _).mpr NNReal.one_ne_zero)
    (hitAtMostOne := NNReal.le_refl _)
    (entrance := Set.univ)
    (fun input _ => by
      rw [(firstMarkov input).univ_eq_one]
      exact ENNReal.le_refl _)
  rw [NNReal.one_mul] at entered
  exact (minorization_on_univ _ _ _ _).mpr entered

/-- A fixed mixture keeps the first component's one-step bound, scaled by the
component's weight. -/
theorem minorization_mixture {first second : Kernel space space}
    {mixing weight : NNReal} {reference : Giry.Law space}
    (mixingPositive : NNReal.lt NNReal.zero mixing)
    (mixingAtMostOne : NNReal.le mixing NNReal.one)
    (minor : Minorization first 1 weight reference)
    (secondMarkov : ∀ input, Measure.IsProbability (second input)) :
    Minorization (mixture mixing first second) 1 (NNReal.mul mixing weight)
      reference where
  markov := mixture_markov mixing mixingAtMostOne first second minor.markov secondMarkov
  stepsPositive := Nat.zero_lt_one
  weightPositive := product_positive mixingPositive minor.weightPositive
  weightAtMostOne := product_at_most_one mixingAtMostOne minor.weightAtMostOne
  lower := by
    intro input event eventMeasurable
    have lower := minor.lower input event eventMeasurable
    rw [iterate_one, Measure.smul_apply_measurable _ _ eventMeasurable] at lower
    rw [iterate_one, Measure.smul_apply_measurable _ _ eventMeasurable, mixture,
      Kernel.add_apply, Measure.add_apply_measurable _ _ eventMeasurable,
      Kernel.smul_apply, Measure.smul_apply_measurable _ _ eventMeasurable,
      ← ENNReal.finite_mul_finite, ENNReal.mul_assoc]
    exact ENNReal.le_trans
      (ENNReal.mul_le_mul (ENNReal.le_refl _) lower)
      (ENNReal.le_self_add _ _)

/-- The weight `mixingᵐ · weight` of a block bound that survives mixing. -/
@[expose] noncomputable def mixtureBlockWeight (mixing : NNReal) :
    Nat → NNReal → NNReal
  | 0, weight => weight
  | steps + 1, weight => NNReal.mul mixing (mixtureBlockWeight mixing steps weight)

theorem mixtureBlockWeight_finite (mixing weight : NNReal) (steps : Nat) :
    ENNReal.finite (mixtureBlockWeight mixing steps weight) =
      ENNReal.mul (ENNReal.pow (ENNReal.finite mixing) steps)
        (ENNReal.finite weight) := by
  induction steps with
  | zero => rw [mixtureBlockWeight, ENNReal.pow_zero, ENNReal.one_mul]
  | succ steps induction =>
      rw [mixtureBlockWeight, ← ENNReal.finite_mul_finite, induction,
        ENNReal.pow_succ, ENNReal.mul_assoc]

/-- The iterates of a fixed mixture dominate the scaled iterates of its first
component. -/
theorem iterate_mixture_lower (first second : Kernel space space)
    (mixing : NNReal) (steps : Nat) (input : α) {event : Set α}
    (eventMeasurable : space.Measurable event) :
    ENNReal.le
      (ENNReal.mul (ENNReal.pow (ENNReal.finite mixing) steps)
        (iterate first steps input event))
      (iterate (mixture mixing first second) steps input event) := by
  induction steps generalizing input with
  | zero =>
      rw [ENNReal.pow_zero, ENNReal.one_mul]
      exact ENNReal.le_refl _
  | succ steps induction =>
      have firstMeasurable := (iterate first steps).measurable eventMeasurable
      have component : ∀ set, space.Measurable set →
          ENNReal.le ((Measure.smul (ENNReal.finite mixing) (first input)) set)
            (mixture mixing first second input set) := by
        intro set setMeasurable
        rw [Measure.smul_apply_measurable _ _ setMeasurable, mixture, Kernel.add_apply,
          Measure.add_apply_measurable _ _ setMeasurable, Kernel.smul_apply,
          Measure.smul_apply_measurable _ _ setMeasurable]
        exact ENNReal.le_self_add _ _
      rw [iterate_succ, iterate_succ, comp_apply_measurable _ _ _ eventMeasurable,
        comp_apply_measurable _ _ _ eventMeasurable, ENNReal.pow_succ, ENNReal.mul_comm
          (ENNReal.finite mixing), ENNReal.mul_assoc, ← lintegral_smul_measure,
        ← lintegral_smul _ _ firstMeasurable]
      exact ENNReal.le_trans (lintegral_mono_measure _ _ _ component)
        (lintegral_mono _ (fun state => induction state))

/-- A fixed mixture keeps the first component's block bound over `steps`,
scaled by the mixing weight's `steps`-th power. -/
theorem minorization_mixture_block {first second : Kernel space space}
    {mixing weight : NNReal} {steps : Nat} {reference : Giry.Law space}
    (mixingPositive : NNReal.lt NNReal.zero mixing)
    (mixingAtMostOne : NNReal.le mixing NNReal.one)
    (minor : Minorization first steps weight reference)
    (secondMarkov : ∀ input, Measure.IsProbability (second input)) :
    Minorization (mixture mixing first second) steps
      (mixtureBlockWeight mixing steps weight) reference where
  markov := mixture_markov mixing mixingAtMostOne first second minor.markov secondMarkov
  stepsPositive := minor.stepsPositive
  weightPositive := by
    have positive := minor.weightPositive
    clear minor secondMarkov
    induction steps with
    | zero => exact positive
    | succ steps induction => exact product_positive mixingPositive induction
  weightAtMostOne := by
    have bounded := minor.weightAtMostOne
    clear minor secondMarkov
    induction steps with
    | zero => exact bounded
    | succ steps induction => exact product_at_most_one mixingAtMostOne induction
  lower := by
    intro input event eventMeasurable
    have lower := minor.lower input event eventMeasurable
    rw [Measure.smul_apply_measurable _ _ eventMeasurable] at lower
    rw [Measure.smul_apply_measurable _ _ eventMeasurable, mixtureBlockWeight_finite,
      ENNReal.mul_assoc]
    exact ENNReal.le_trans (ENNReal.mul_le_mul (ENNReal.le_refl _) lower)
      (iterate_mixture_lower first second mixing steps input eventMeasurable)

end

end Problib.Measure.Kernel
