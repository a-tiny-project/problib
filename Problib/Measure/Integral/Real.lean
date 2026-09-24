module

public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

/-! Finite signed real integrals certified by measurable nonnegative parts.
Both part integrals are finite before subtraction. The parts need not be the
canonical positive and negative parts; uniqueness proves the result independent
of the chosen decomposition. -/

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real

universe u
variable {α : Type u} {space : Space α}

/-- A finite nonnegative decomposition of a real integrand, including evaluated
lower integrals for both parts. The pointwise equation is stronger than an
almost-everywhere decomposition and makes this certificate easy to compose. -/
public structure IntegralParts (measure : Measure space) (integrand : α → Carrier) where
  positive : α → NNReal
  negative : α → NNReal
  positive_measurable : ENNRealMeasurable space (fun x => ENNReal.finite (positive x))
  negative_measurable : ENNRealMeasurable space (fun x => ENNReal.finite (negative x))
  decomposition : ∀ x, integrand x = sub (positive x).toReal (negative x).toReal
  positiveMass : NNReal
  negativeMass : NNReal
  positive_integral : lintegral measure (fun x => ENNReal.finite (positive x)) =
    ENNReal.finite positiveMass
  negative_integral : lintegral measure (fun x => ENNReal.finite (negative x)) =
    ENNReal.finite negativeMass

namespace IntegralParts

/-- Subtract only already finite, evaluated nonnegative integrals. -/
@[expose] public def value {measure : Measure space} {integrand : α → Carrier}
    (parts : IntegralParts measure integrand) : Carrier :=
  sub parts.positiveMass.toReal parts.negativeMass.toReal

private theorem cross_of_sub {a b c d : Carrier} (equal : sub a b = sub c d) :
    add a d = add c b := by
  have h := congrArg (fun x => add (add x b) d) equal
  rw [sub_add_cancel, add_assoc (sub c d) b d, add_comm b d, ← add_assoc, sub_add_cancel] at h
  exact h

private theorem sub_of_cross {a b c d : Carrier} (equal : add a d = add c b) :
    sub a b = sub c d := by
  apply add_right_cancel (right := b)
  apply add_right_cancel (right := d)
  rw [sub_add_cancel, add_assoc (sub c d) b d, add_comm b d, ← add_assoc, sub_add_cancel]
  exact equal

/-- Signed integration does not depend on a particular finite decomposition.
No extended-real infinity cancellation is used. -/
public theorem unique {measure : Measure space} {integrand : α → Carrier}
    (left right : IntegralParts measure integrand) : left.value = right.value := by
  have same : (fun x => ENNReal.add (ENNReal.finite (left.positive x))
      (ENNReal.finite (right.negative x))) =
      (fun x => ENNReal.add (ENNReal.finite (right.positive x))
        (ENNReal.finite (left.negative x))) := by
    funext x
    apply congrArg ENNReal.finite
    apply NNReal.ext
    exact cross_of_sub ((left.decomposition x).symm.trans (right.decomposition x))
  have integrals := congrArg (lintegral measure) same
  rw [lintegral_add _ left.positive_measurable right.negative_measurable,
    lintegral_add _ right.positive_measurable left.negative_measurable,
    left.positive_integral, left.negative_integral,
    right.positive_integral, right.negative_integral] at integrals
  have finiteEqual := ENNReal.finite_injective integrals
  exact sub_of_cross (congrArg NNReal.toReal finiteEqual)

/-- Positive and negative parts reconstruct every real scalar. -/
public theorem scalar_decomposition (scalar : Carrier) :
    scalar = sub (NNReal.ofReal scalar).toReal (NNReal.ofReal (neg scalar)).toReal := by
  rcases le_total zero scalar with nonnegative | nonpositive
  · have hn : le (neg scalar) zero := by
      simpa only [neg_zero] using neg_le_neg_iff.mpr nonnegative
    rw [NNReal.toReal_ofReal nonnegative, NNReal.ofReal_eq_zero_iff.mpr hn,
      NNReal.toReal_zero, sub_eq_add_neg, neg_zero, add_zero]
  · have hn : le zero (neg scalar) := by
      simpa only [neg_zero] using neg_le_neg_iff.mpr nonpositive
    rw [NNReal.toReal_ofReal hn, NNReal.ofReal_eq_zero_iff.mpr nonpositive,
      NNReal.toReal_zero, sub_eq_add_neg, neg_neg, add_comm zero, add_zero]

/-- Constants have their stated integral under a probability measure. -/
@[expose] public noncomputable def const {measure : Measure space}
    (probability : Measure.IsProbability measure) (scalar : Carrier) :
    IntegralParts measure (fun _ => scalar) where
  positive := fun _ => NNReal.ofReal scalar
  negative := fun _ => NNReal.ofReal (neg scalar)
  positive_measurable := ENNRealMeasurable.constant _ _
  negative_measurable := ENNRealMeasurable.constant _ _
  decomposition := fun _ => scalar_decomposition scalar
  positiveMass := NNReal.ofReal scalar
  negativeMass := NNReal.ofReal (neg scalar)
  positive_integral := by rw [lintegral_const, probability.univ_eq_one, ENNReal.mul_one]
  negative_integral := by rw [lintegral_const, probability.univ_eq_one, ENNReal.mul_one]

public theorem const_value {measure : Measure space} (probability : Measure.IsProbability measure)
    (scalar : Carrier) : (const probability scalar).value = scalar :=
  (scalar_decomposition scalar).symm

/-- Add finite decompositions without choosing new positive and negative parts. -/
@[expose] public noncomputable def addParts {measure : Measure space} {f g : α → Carrier}
    (left : IntegralParts measure f) (right : IntegralParts measure g) :
    IntegralParts measure (fun x => add (f x) (g x)) where
  positive := fun x => NNReal.add (left.positive x) (right.positive x)
  negative := fun x => NNReal.add (left.negative x) (right.negative x)
  positive_measurable := left.positive_measurable.add right.positive_measurable
  negative_measurable := left.negative_measurable.add right.negative_measurable
  decomposition := fun x => by
    rw [left.decomposition x, right.decomposition x]
    exact (add_sub_add_comm _ _ _ _).symm
  positiveMass := NNReal.add left.positiveMass right.positiveMass
  negativeMass := NNReal.add left.negativeMass right.negativeMass
  positive_integral := by
    change lintegral measure (fun x => ENNReal.add (ENNReal.finite (left.positive x))
      (ENNReal.finite (right.positive x))) = _
    rw [lintegral_add _ left.positive_measurable right.positive_measurable,
      left.positive_integral, right.positive_integral]
    rfl
  negative_integral := by
    change lintegral measure (fun x => ENNReal.add (ENNReal.finite (left.negative x))
      (ENNReal.finite (right.negative x))) = _
    rw [lintegral_add _ left.negative_measurable right.negative_measurable,
      left.negative_integral, right.negative_integral]
    rfl

public theorem addParts_value {measure : Measure space} {f g : α → Carrier}
    (left : IntegralParts measure f) (right : IntegralParts measure g) :
    (left.addParts right).value = add left.value right.value :=
  add_sub_add_comm _ _ _ _

/-- Transport a certificate across pointwise equality of integrands. -/
@[expose] public def congr {measure : Measure space} {f g : α → Carrier}
    (parts : IntegralParts measure f) (equal : ∀ x, f x = g x) : IntegralParts measure g :=
  { parts with decomposition := fun x => (equal x).symm.trans (parts.decomposition x) }

public theorem congr_value {measure : Measure space} {f g : α → Carrier}
    (parts : IntegralParts measure f) (equal : ∀ x, f x = g x) :
    (parts.congr equal).value = parts.value := rfl

/-- A nonnegative scalar preserves the finite positive and negative decomposition. -/
@[expose] public noncomputable def smulNonnegative {measure : Measure space} {f : α → Carrier}
    (parts : IntegralParts measure f) (scalar : NNReal) :
    IntegralParts measure (fun value => mul scalar.toReal (f value)) where
  positive := fun value => NNReal.mul scalar (parts.positive value)
  negative := fun value => NNReal.mul scalar (parts.negative value)
  positive_measurable := (ENNRealMeasurable.constant space (ENNReal.finite scalar)).mul parts.positive_measurable
  negative_measurable := (ENNRealMeasurable.constant space (ENNReal.finite scalar)).mul parts.negative_measurable
  decomposition := fun value => by
    rw [parts.decomposition value]
    exact mul_sub _ _ _
  positiveMass := NNReal.mul scalar parts.positiveMass
  negativeMass := NNReal.mul scalar parts.negativeMass
  positive_integral := by
    change lintegral measure (fun value => ENNReal.mul (ENNReal.finite scalar) (ENNReal.finite (parts.positive value))) = _
    rw [lintegral_smul _ _ parts.positive_measurable, parts.positive_integral]
    rfl
  negative_integral := by
    change lintegral measure (fun value => ENNReal.mul (ENNReal.finite scalar) (ENNReal.finite (parts.negative value))) = _
    rw [lintegral_smul _ _ parts.negative_measurable, parts.negative_integral]
    rfl

public theorem smulNonnegative_value {measure : Measure space} {f : α → Carrier}
    (parts : IntegralParts measure f) (scalar : NNReal) :
    (parts.smulNonnegative scalar).value = mul scalar.toReal parts.value :=
  (mul_sub _ _ _).symm

/-- Negation swaps the evaluated finite parts. -/
@[expose] public def negParts {measure : Measure space} {f : α → Carrier}
    (parts : IntegralParts measure f) : IntegralParts measure (fun value => neg (f value)) where
  positive := parts.negative
  negative := parts.positive
  positive_measurable := parts.negative_measurable
  negative_measurable := parts.positive_measurable
  decomposition := fun value => by rw [parts.decomposition]; exact neg_sub _ _
  positiveMass := parts.negativeMass
  negativeMass := parts.positiveMass
  positive_integral := parts.negative_integral
  negative_integral := parts.positive_integral

public theorem negParts_value {measure : Measure space} {f : α → Carrier} (parts : IntegralParts measure f) :
    parts.negParts.value = neg parts.value := (neg_sub _ _).symm

/-- Every real scalar acts on finite signed integral certificates, including zero and negative scalars. -/
@[expose] public noncomputable def smul {measure : Measure space} {f : α → Carrier}
    (parts : IntegralParts measure f) (scalar : Carrier) : IntegralParts measure (fun value => mul scalar (f value)) := by
  classical
  exact if nonnegative : le zero scalar then
    (parts.smulNonnegative ⟨scalar, nonnegative⟩)
  else
    (parts.negParts.smulNonnegative ⟨neg scalar, by
      have nonpositive := (le_total zero scalar).resolve_left nonnegative
      simpa only [neg_zero] using neg_le_neg_iff.mpr nonpositive⟩).congr
      (fun value => multiplicativeSelection.ring.neg_mul_neg scalar (f value))

public theorem smul_value {measure : Measure space} {f : α → Carrier}
    (parts : IntegralParts measure f) (scalar : Carrier) : (parts.smul scalar).value = mul scalar parts.value := by
  classical
  unfold smul
  split
  · exact smulNonnegative_value _ _
  · rw [congr_value, smulNonnegative_value, negParts_value]
    exact multiplicativeSelection.ring.neg_mul_neg _ _

/-- A certified integrand is Borel measurable: it is the difference of the
real projections of its two measurable parts. -/
public theorem measurable {measure : Measure space} {integrand : α → Carrier}
    (parts : IntegralParts measure integrand) : MeasurableMap space borel integrand := by
  have positive : MeasurableMap space borel (fun x => (parts.positive x).toReal) :=
    MeasurableMap.comp toReal_measurable parts.positive_measurable.measurableMap
  have negative : MeasurableMap space borel (fun x => (parts.negative x).toReal) :=
    MeasurableMap.comp toReal_measurable parts.negative_measurable.measurableMap
  have same : integrand = fun x => sub (parts.positive x).toReal (parts.negative x).toReal :=
    funext parts.decomposition
  rw [same]
  intro set measurableSet
  exact measurable_sub positive negative measurableSet

/-- The positive and negative parts of a measurable integrand certify its
integral once both part integrals are finite. -/
@[expose] public noncomputable def canonical {measure : Measure space} {integrand : α → Carrier}
    (measurable : MeasurableMap space borel integrand)
    (positiveFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (integrand x))))
    (negativeFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (neg (integrand x))))) :
    IntegralParts measure integrand where
  positive := fun x => NNReal.ofReal (integrand x)
  negative := fun x => NNReal.ofReal (neg (integrand x))
  positive_measurable := ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable measurable
  negative_measurable := ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
    (by
      intro set measurableSet
      exact MeasurableMap.comp neg_measurable measurable measurableSet)
  decomposition := fun x => scalar_decomposition (integrand x)
  positiveMass := Classical.choose (ENNReal.exists_finite_of_finite positiveFinite)
  negativeMass := Classical.choose (ENNReal.exists_finite_of_finite negativeFinite)
  positive_integral := Classical.choose_spec (ENNReal.exists_finite_of_finite positiveFinite)
  negative_integral := Classical.choose_spec (ENNReal.exists_finite_of_finite negativeFinite)

end IntegralParts

/-- A finite signed integral value, certified independently of the decomposition
used to derive it. No convention for nonintegrable functions is introduced. -/
@[expose] public def HasRealIntegral (measure : Measure space) (integrand : α → Carrier) (value : Carrier) : Prop :=
  ∃ parts : IntegralParts measure integrand, parts.value = value

public theorem HasRealIntegral.unique {measure : Measure space} {integrand : α → Carrier}
    {left right : Carrier} (first : HasRealIntegral measure integrand left)
    (second : HasRealIntegral measure integrand right) : left = right := by
  obtain ⟨first, firstValue⟩ := first
  obtain ⟨second, secondValue⟩ := second
  exact firstValue.symm.trans ((first.unique second).trans secondValue)

/-- Certified integrals transport across pointwise equality of integrands. -/
public theorem HasRealIntegral.congr {measure : Measure space} {f g : α → Carrier}
    {value : Carrier} (integral : HasRealIntegral measure f value)
    (equal : ∀ x, f x = g x) : HasRealIntegral measure g value := by
  obtain ⟨parts, same⟩ := integral
  exact ⟨parts.congr equal, same⟩

/-- Certified integrals add. -/
public theorem HasRealIntegral.add {measure : Measure space} {f g : α → Carrier}
    {left right : Carrier} (first : HasRealIntegral measure f left)
    (second : HasRealIntegral measure g right) :
    HasRealIntegral measure (fun x => Construction.Dedekind.add (f x) (g x)) (Construction.Dedekind.add left right) := by
  obtain ⟨first, firstValue⟩ := first
  obtain ⟨second, secondValue⟩ := second
  exact ⟨first.addParts second, by rw [IntegralParts.addParts_value, firstValue, secondValue]⟩

/-- Certified integrals negate. -/
public theorem HasRealIntegral.neg {measure : Measure space} {f : α → Carrier}
    {value : Carrier} (integral : HasRealIntegral measure f value) :
    HasRealIntegral measure (fun x => Construction.Dedekind.neg (f x)) (Construction.Dedekind.neg value) := by
  obtain ⟨parts, same⟩ := integral
  exact ⟨parts.negParts, by rw [IntegralParts.negParts_value, same]⟩

/-- Certified integrals subtract. -/
public theorem HasRealIntegral.sub {measure : Measure space} {f g : α → Carrier}
    {left right : Carrier} (first : HasRealIntegral measure f left)
    (second : HasRealIntegral measure g right) :
    HasRealIntegral measure (fun x => Construction.Dedekind.sub (f x) (g x)) (Construction.Dedekind.sub left right) := by
  have combined := first.add second.neg
  rw [← sub_eq_add_neg] at combined
  exact combined.congr (fun x => (sub_eq_add_neg (f x) (g x)).symm)

/-- Certified integrals scale by every real scalar. -/
public theorem HasRealIntegral.smul {measure : Measure space} {f : α → Carrier}
    {value : Carrier} (integral : HasRealIntegral measure f value) (scalar : Carrier) :
    HasRealIntegral measure (fun x => mul scalar (f x)) (mul scalar value) := by
  obtain ⟨parts, same⟩ := integral
  exact ⟨parts.smul scalar, by rw [IntegralParts.smul_value, same]⟩

/-- Scaling a measure scales a finite signed integral by the same factor. Both
parts scale, and the value is their difference. -/
public theorem smul_hasRealIntegral {β : Type} {carrier : Space β} (measure : Measure carrier)
    (integrand : β → Carrier) {value : Carrier} (factor : NNReal)
    (integral : HasRealIntegral measure integrand value) :
    HasRealIntegral (Measure.smul (ENNReal.finite factor) measure) integrand
      (mul factor.toReal value) := by
  obtain ⟨parts, same⟩ := integral
  refine ⟨{ positive := parts.positive
            negative := parts.negative
            positive_measurable := parts.positive_measurable
            negative_measurable := parts.negative_measurable
            decomposition := parts.decomposition
            positiveMass := NNReal.mul factor parts.positiveMass
            negativeMass := NNReal.mul factor parts.negativeMass
            positive_integral := by
              rw [lintegral_smul_measure, parts.positive_integral]
              rfl
            negative_integral := by
              rw [lintegral_smul_measure, parts.negative_integral]
              rfl }, ?_⟩
  show Construction.Dedekind.sub (NNReal.mul factor parts.positiveMass).toReal
      (NNReal.mul factor parts.negativeMass).toReal = mul factor.toReal value
  rw [NNReal.toReal_mul, NNReal.toReal_mul, ← same]
  exact (IntegralParts.smulNonnegative_value parts factor).symm ▸ rfl

/-- A nonnegative integrand's certified integral is its lower integral, read
through the embedding of the reals into the extended nonnegative reals. The
canonical decomposition of a nonnegative integrand has a zero negative part, so
its positive mass is the certified value. -/
public theorem HasRealIntegral.lintegral_ofReal {measure : Measure space}
    {integrand : α → Carrier} {value : Carrier}
    (nonnegative : ∀ x, le zero (integrand x))
    (integral : HasRealIntegral measure integrand value) :
    lintegral measure (fun x => ENNReal.ofReal (integrand x)) = ENNReal.ofReal value := by
  obtain ⟨parts, same⟩ := integral
  have belowPositive : ∀ x, ENNReal.le (ENNReal.ofReal (integrand x))
      (ENNReal.finite (parts.positive x)) := by
    intro x
    rw [← ENNReal.ofReal_toReal_finite (parts.positive x)]
    apply ENNReal.ofReal_monotone
    rw [parts.decomposition x, sub_eq_add_neg]
    have dropped := add_le_add_left_iff (shift := (parts.positive x).toReal).mpr
      (neg_nonpositive_iff.mp (parts.negative x).property)
    rwa [add_zero] at dropped
  have vanishes : (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x))) = fun _ => ENNReal.zero := by
    funext x
    apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_monotone (neg_nonpositive_iff.mp (nonnegative x))
  have positiveFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (integrand x))) :=
    ENNReal.finite_of_le (lintegral_mono measure belowPositive)
      (by rw [parts.positive_integral]; exact True.intro)
  have negativeFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x)))) := by
    rw [vanishes, lintegral_zero]
    exact True.intro
  let canonical := IntegralParts.canonical parts.measurable positiveFinite negativeFinite
  have negativeMass : canonical.negativeMass = NNReal.zero := by
    have integralZero := canonical.negative_integral
    change lintegral measure (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x))) = _ at integralZero
    rw [vanishes, lintegral_zero] at integralZero
    exact (ENNReal.finite_injective integralZero).symm
  have valueEqual : canonical.value = value := (canonical.unique parts).trans same
  have positiveIntegral := canonical.positive_integral
  change lintegral measure (fun x => ENNReal.ofReal (integrand x)) = _ at positiveIntegral
  rw [positiveIntegral, ← valueEqual]
  unfold IntegralParts.value
  rw [negativeMass]
  change _ = ENNReal.ofReal (Construction.Dedekind.sub canonical.positiveMass.toReal zero)
  rw [sub_eq_add_neg, neg_zero, add_zero]
  exact (ENNReal.ofReal_toReal_finite canonical.positiveMass).symm

section Transport

variable {β : Type u} {target : Space β}

/-- Parts of an integrand against a pushforward pull back along its map. Each
part composes with the map, and `lintegral_map` keeps both masses, so the
value is unchanged. -/
@[expose] public def IntegralParts.comap {measure : Measure space} {before : α → β}
    (beforeMeasurable : MeasurableMap space target before) {f : β → Carrier}
    (parts : IntegralParts (measure.map before beforeMeasurable) f) :
    IntegralParts measure (fun x => f (before x)) where
  positive := fun x => parts.positive (before x)
  negative := fun x => parts.negative (before x)
  positive_measurable := ENNRealMeasurable.comp
    (map := fun y => ENNReal.finite (parts.positive y)) parts.positive_measurable beforeMeasurable
  negative_measurable := ENNRealMeasurable.comp
    (map := fun y => ENNReal.finite (parts.negative y)) parts.negative_measurable beforeMeasurable
  decomposition := fun x => parts.decomposition (before x)
  positiveMass := parts.positiveMass
  negativeMass := parts.negativeMass
  positive_integral :=
    (lintegral_map measure before beforeMeasurable parts.positive_measurable).symm.trans
      parts.positive_integral
  negative_integral :=
    (lintegral_map measure before beforeMeasurable parts.negative_measurable).symm.trans
      parts.negative_integral

public theorem IntegralParts.comap_value {measure : Measure space} {before : α → β}
    (beforeMeasurable : MeasurableMap space target before) {f : β → Carrier}
    (parts : IntegralParts (measure.map before beforeMeasurable) f) :
    (parts.comap beforeMeasurable).value = parts.value := rfl

/-- An integrand with finite parts has a finite positive part: it lies below
the part that certifies it. -/
private theorem IntegralParts.positive_finite {measure : Measure space} {g : α → Carrier}
    (parts : IntegralParts measure g) :
    ENNReal.Finite (lintegral measure (fun x => ENNReal.ofReal (g x))) := by
  have below : ∀ x, ENNReal.le (ENNReal.ofReal (g x)) (ENNReal.finite (parts.positive x)) := by
    intro x
    rw [parts.decomposition x]
    have nonnegative : le zero (parts.negative x).toReal := (parts.negative x).2
    have lowered : le (sub (parts.positive x).toReal (parts.negative x).toReal)
        (parts.positive x).toReal := by
      rw [sub_eq_add_neg]
      have negative : le (neg (parts.negative x).toReal) zero := by
        have flipped := (neg_le_neg_iff (left := zero)).mpr nonnegative
        rwa [Problib.Real.Construction.Dedekind.neg_zero] at flipped
      have shifted := (add_le_add_left_iff (shift := (parts.positive x).toReal)).mpr negative
      rwa [add_zero] at shifted
    have monotone := NNReal.ofReal_monotone lowered
    rw [NNReal.ofReal_toReal] at monotone
    exact monotone
  refine ENNReal.finite_of_le (lintegral_mono measure below) ?_
  rw [parts.positive_integral]
  exact True.intro

/-- A certified integral moves to a pushforward: integrating a measurable `f`
against `measure.map before` is integrating `f ∘ before` against `measure`. -/
public theorem HasRealIntegral.map {measure : Measure space} {before : α → β}
    (beforeMeasurable : MeasurableMap space target before) {f : β → Carrier}
    (measurable : MeasurableMap target borel f) {value : Carrier}
    (integral : HasRealIntegral measure (fun x => f (before x)) value) :
    HasRealIntegral (measure.map before beforeMeasurable) f value := by
  obtain ⟨parts, same⟩ := integral
  have positiveMeasurable : ENNRealMeasurable target (fun y => ENNReal.ofReal (f y)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable measurable
  have negativeMeasurable : ENNRealMeasurable target (fun y => ENNReal.ofReal (Construction.Dedekind.neg (f y))) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (by
        intro set measurableSet
        exact MeasurableMap.comp neg_measurable measurable measurableSet)
  have positiveFinite := IntegralParts.positive_finite parts
  have negativeFinite := IntegralParts.positive_finite parts.negParts
  rw [← lintegral_map measure before beforeMeasurable positiveMeasurable] at positiveFinite
  rw [← lintegral_map measure before beforeMeasurable negativeMeasurable] at negativeFinite
  let canonical := IntegralParts.canonical measurable positiveFinite negativeFinite
  refine ⟨canonical, ?_⟩
  rw [← same]
  rw [← IntegralParts.comap_value beforeMeasurable canonical]
  exact (canonical.comap beforeMeasurable).unique parts

end Transport

end Problib.Measure
