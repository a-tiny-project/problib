module
public import Problib.Measure.Configuration.Power
public import Problib.Measure.Additive.Sum
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real
public section
universe u
variable {α : Type u} {element : Space α}

@[expose] public def factorial : Nat → Nat
  | 0 => 1
  | count + 1 => (count + 1) * factorial count

@[expose] public noncomputable def labelled : Nat → NNReal := fun _ => NNReal.one

/-- Janossy convention: coefficient `1/n!` on the ordered iid power. -/
@[expose] public noncomputable def janossy : Nat → NNReal :=
  fun count => NNReal.div NNReal.one
    (NNReal.ofReal (Problib.Real.Construction.Dedekind.selection.ofRat
      (factorial count : Rat)))

/-- At a merge-side length `n′`, the split-side length is `n′ + k - l`.
The reference change uses `c(split length)/c(merge length)`. -/
@[expose] public noncomputable def coefficientRatio (coefficient : Nat → NNReal)
    (removed inserted mergeLength : Nat) : NNReal :=
  NNReal.div (coefficient (mergeLength + removed - inserted))
    (coefficient mergeLength)

/-- Declared count coefficients multiply ordered iid powers. -/
@[expose] public noncomputable def configurationReference
    (reference : Measure element) (finite : Measure.SFinite reference)
    (coefficient : Nat → NNReal) : Measure (Space.list element) :=
  Measure.sum (fun count => Measure.smul (ENNReal.finite (coefficient count))
    (Measure.listPower reference finite count))

private theorem listPower_restrict_length_null (reference : Measure element)
    (finite : Measure.SFinite reference) (count : Nat) (region : Set (List α)) :
    ((Measure.listPower reference finite count).restrict region).NullSet
      (fun values => values.length ≠ count) := by
  have lengthMeasurable : (Space.list element).Measurable
      (fun values : List α => values.length ≠ count) :=
    ListSpace.length_measurable element (set := fun length => length ≠ count) trivial
  unfold Measure.NullSet
  rw [Measure.restrict_apply _ _ lengthMeasurable]
  exact Measure.NullSet.mono (Measure.listPower_length_null reference finite count)
    (fun {_} inside => inside.1)

private theorem listPower_restrict_lintegral_congr (reference : Measure element)
    (finite : Measure.SFinite reference) (count : Nat) (region : Set (List α))
    {left right : List α → ENNReal}
    (equal : ∀ values, values.length = count → left values = right values) :
    lintegral ((Measure.listPower reference finite count).restrict region) left =
      lintegral ((Measure.listPower reference finite count).restrict region) right :=
  lintegral_congr_ae (Measure.NullSet.mono
    (listPower_restrict_length_null reference finite count region)
    (fun {values} failure lengthEqual => failure (equal values lengthEqual)))

/-- Changing count coefficients is a density: the ratio of the new coefficient
to the old one at each length. -/
public theorem configurationReference_rescale (reference : Measure element)
    (finite : Measure.SFinite reference) {first second : Nat → NNReal}
    (positive : ∀ count, NNReal.lt NNReal.zero (first count)) :
    (configurationReference reference finite first).withDensity (fun values =>
        ENNReal.finite (NNReal.div (second values.length) (first values.length))) =
      configurationReference reference finite second := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable, configurationReference,
    configurationReference, Measure.restrict_sum _ setMeasurable, lintegral_sum,
    Measure.sum_apply _ setMeasurable]
  apply ENNReal.tsum_congr
  intro count
  have integrand : lintegral
      ((Measure.listPower reference finite count).restrict set)
      (fun values => ENNReal.finite
        (NNReal.div (second values.length) (first values.length))) =
      lintegral ((Measure.listPower reference finite count).restrict set)
        (fun _ => ENNReal.finite (NNReal.div (second count) (first count))) :=
    listPower_restrict_lintegral_congr reference finite count set
      (fun values lengthEqual => by rw [lengthEqual])
  rw [Measure.restrict_smul _ _ setMeasurable, lintegral_smul_measure, integrand,
    lintegral_const, Measure.restrict_apply_univ,
    Measure.smul_apply_measurable _ _ setMeasurable, ← ENNReal.mul_assoc,
    ENNReal.finite_mul_finite,
    NNReal.mul_div_cancel _ ((NNReal.zero_lt_iff_ne_zero _).mp (positive count))]

/-- Component references: a law given count by count by densities against
the iid powers has density `p_n / c_n` against the configuration
reference. -/
public theorem component_density (reference : Measure element)
    (finite : Measure.SFinite reference) {coefficient : Nat → NNReal}
    (positive : ∀ count, NNReal.lt NNReal.zero (coefficient count))
    {law : Measure (Space.list element)} {density : Nat → List α → ENNReal}
    (densityMeasurable : ∀ count,
      ENNRealMeasurable (Space.list element) (density count))
    (components : ∀ count,
      law.restrict (fun values => values.length = count) =
        (Measure.listPower reference finite count).withDensity (density count)) :
    law = (configurationReference reference finite coefficient).withDensity
      (fun values => ENNReal.mul (density values.length values)
        (ENNReal.finite (NNReal.div NNReal.one (coefficient values.length)))) := by
  have fiber : ∀ count, (Space.list element).Measurable
      (fun values : List α => values.length = count) :=
    fun count => ListSpace.length_measurable element
      (set := fun length => length = count) trivial
  have split : law = Measure.sum
      (fun count => law.restrict (fun values => values.length = count)) := by
    rw [← Measure.restrict_iUnion law _ fiber
      (fun first second different values inFirst inSecond =>
        different (inFirst.symm.trans inSecond))]
    have whole : Set.iUnion (fun count => fun values : List α =>
        values.length = count) = Set.univ :=
      funext fun values => propext ⟨fun _ => True.intro,
        fun _ => ⟨values.length, rfl⟩⟩
    rw [whole, Measure.restrict_univ]
  rw [split]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.sum_apply _ setMeasurable, Measure.withDensity_apply _ _ setMeasurable,
    configurationReference, Measure.restrict_sum _ setMeasurable, lintegral_sum]
  apply ENNReal.tsum_congr
  intro count
  have integrand : lintegral
      ((Measure.listPower reference finite count).restrict set)
      (fun values => ENNReal.mul (density values.length values)
        (ENNReal.finite (NNReal.div NNReal.one (coefficient values.length)))) =
      lintegral ((Measure.listPower reference finite count).restrict set)
        (fun values => ENNReal.mul
          (ENNReal.finite (NNReal.div NNReal.one (coefficient count)))
          (density count values)) :=
    listPower_restrict_lintegral_congr reference finite count set
      (fun values lengthEqual => by rw [lengthEqual, ENNReal.mul_comm])
  rw [components count, Measure.withDensity_apply _ _ setMeasurable,
    Measure.restrict_smul _ _ setMeasurable, lintegral_smul_measure, integrand,
    lintegral_smul _ _ (densityMeasurable count), ← ENNReal.mul_assoc,
    ENNReal.finite_mul_finite,
    NNReal.mul_div_cancel _ ((NNReal.zero_lt_iff_ne_zero _).mp (positive count))]
  exact (ENNReal.one_mul _).symm


/-- The configuration reference is s-finite, as a countable sum of scaled
s-finite powers. -/
public noncomputable def Measure.SFinite.configurationReference (reference : Measure element)
    (finite : Measure.SFinite reference) (coefficient : Nat → NNReal) :
    Measure.SFinite (configurationReference reference finite coefficient) :=
  Measure.SFinite.sum _ (fun count =>
    (Measure.SFinite.listPower finite count).smul (ENNReal.finite (coefficient count))
      True.intro)

/-- Reversal preserves the configuration reference. -/
public theorem configurationReference_reverse (reference : Measure element)
    (finite : Measure.SFinite reference) (coefficient : Nat → NNReal) :
    (configurationReference reference finite coefficient).map List.reverse
        (reverse_measurable element) =
      configurationReference reference finite coefficient := by
  unfold configurationReference
  rw [Measure.map_sum]
  congr 1
  funext count
  rw [Measure.map_smul, Measure.listPower_reverse]

end
end Problib.Measure
