import Foundations.Probability.Finite.PMF
import Foundations.Probability.NNRat.Real
import Foundations.Measure.Normalization
import Foundations.Measure.Kernel.Composition.Bind

set_option autoImplicit false

namespace Foundations.Probability

open Foundations.Measure Foundations.Real

universe u v

namespace FiniteMeasure

variable {alpha : Type u} {beta : Type v}

/-- Interpret a rational-weighted finite table as a measure on an explicit measurable space,
summing weighted Dirac measures. Joins finite probability with continuous measure foundations. -/
noncomputable def toMeasure (space : Space alpha)
    (measure : FiniteMeasure alpha) : Measure space :=
  measure.weights.foldr (fun entry rest => Measure.add
    (Measure.smul (entry.2.toENNReal)
      (Measure.dirac space entry.1)) rest) (Measure.zero space)

/-- The zero finite table interprets as the zero measure. -/
@[simp] theorem toMeasure_zero (space : Space alpha) :
    (0 : FiniteMeasure alpha).toMeasure space = Measure.zero space := rfl

/-- Consing an entry adds a weighted Dirac measure to the interpreted tail measure. -/
theorem toMeasure_cons (space : Space alpha) (value : alpha) (weight : NNRat)
    (rest : List (alpha × NNRat)) :
    (FiniteMeasure.mk ((value, weight) :: rest)).toMeasure space =
      Measure.add (Measure.smul (weight.toENNReal)
        (Measure.dirac space value)) ((FiniteMeasure.mk rest).toMeasure space) := rfl

/-- A Dirac table entry interprets as the Dirac measure at that point. -/
@[simp] theorem toMeasure_dirac (space : Space alpha) (value : alpha) :
    (dirac value).toMeasure space = Measure.dirac space value := by
  change Measure.add (Measure.smul ((1 : NNRat).toENNReal) (Measure.dirac space value))
    (Measure.zero space) = _
  rw [NNRat.toENNReal_one, Measure.one_smul, Measure.add_zero]

/-- Table addition interprets as measure addition. -/
theorem toMeasure_add (space : Space alpha) (left right : FiniteMeasure alpha) :
    (left + right).toMeasure space = Measure.add (left.toMeasure space) (right.toMeasure space) := by
  cases left with
  | mk weights =>
    induction weights with
    | nil => exact (Measure.zero_add _).symm
    | cons head tail induction =>
      change Measure.add _ ((FiniteMeasure.mk tail + right).toMeasure space) =
        Measure.add (Measure.add _ _) _
      rw [induction, Measure.add_assoc]
      rfl

/-- Nonnegative rational scaling of a table interprets as scalar multiplication of the measure. -/
theorem toMeasure_scale (space : Space alpha) (factor : NNRat) (measure : FiniteMeasure alpha) :
    (measure.scale factor).toMeasure space =
      Measure.smul (factor.toENNReal) (measure.toMeasure space) := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil =>
      change Measure.zero space = Measure.smul factor.toENNReal (Measure.zero space)
      apply Measure.ext
      intro set measurable
      rw [Measure.smul_apply_measurable _ _ measurable, Measure.zero_apply, ENNReal.mulZero]
    | cons head tail induction =>
      change Measure.add (Measure.smul (factor * head.2).toENNReal (Measure.dirac space head.1))
        ((FiniteMeasure.mk tail).scale factor |>.toMeasure space) =
        Measure.smul factor.toENNReal (Measure.add
          (Measure.smul head.2.toENNReal (Measure.dirac space head.1))
          ((FiniteMeasure.mk tail).toMeasure space))
      rw [Measure.smul_add, NNRat.toENNReal_mul, induction, Measure.smul_smul]

/-- The total mass of the interpreted measure equals the table total embedded in `ENNReal`. -/
theorem toMeasure_univ (space : Space alpha) (measure : FiniteMeasure alpha) :
    measure.toMeasure space Set.univ = measure.total.toENNReal := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (Measure.zero_apply _).trans NNRat.toENNReal_zero.symm
    | cons head tail induction =>
      change Measure.add (Measure.smul head.2.toENNReal (Measure.dirac space head.1))
        ((FiniteMeasure.mk tail).toMeasure space) Set.univ =
        (head.2 + (FiniteMeasure.mk tail).total).toENNReal
      rw [Measure.add_apply_measurable _ _ space.univ,
        Measure.smul_apply_measurable _ _ space.univ, Measure.dirac_apply_univ,
        ENNReal.mulOne, induction, NNRat.toENNReal_add]

/-- Every interpreted finite table yields a finite measure. -/
theorem toMeasure_isFinite (space : Space alpha) (measure : FiniteMeasure alpha) :
    Measure.IsFinite (measure.toMeasure space) := by
  constructor
  rw [toMeasure_univ]
  exact NNRat.toENNReal_finite _

/-- An interpreted normalized table (total mass 1) yields an exact probability measure. -/
theorem toMeasure_isProbability (space : Space alpha) (measure : FiniteMeasure alpha)
    (total : measure.total = 1) : Measure.IsProbability (measure.toMeasure space) := by
  constructor
  rw [toMeasure_univ, total]
  exact NNRat.toENNReal_one

/-- Interpretation commutes with pushforward along a measurable map. -/
theorem toMeasure_map {source : Space alpha} {target : Space beta}
    (measure : FiniteMeasure alpha) (function : alpha → beta)
    (measurable : MeasurableMap source target function) :
    (measure.map function).toMeasure target = (measure.toMeasure source).map function measurable := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (Measure.map_zero function measurable).symm
    | cons head tail induction =>
      change Measure.add _ (((FiniteMeasure.mk tail).map function).toMeasure target) =
        (Measure.add _ _).map function measurable
      rw [Measure.map_add, Measure.map_smul, Measure.map_dirac, induction]
      rfl

/-- Interpretation commutes with bind against a measurable kernel with matching fibers. -/
theorem toMeasure_bind {source : Space alpha} {target : Space beta}
    (measure : FiniteMeasure alpha) (family : alpha → FiniteMeasure beta)
    (kernel : Kernel source target) (represents : ∀ value, (family value).toMeasure target = kernel value) :
    (measure.bind family).toMeasure target = (measure.toMeasure source).bind kernel := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (Measure.zero_bind kernel).symm
    | cons head tail induction =>
      change (((family head.1).scale head.2) + (FiniteMeasure.mk tail).bind family).toMeasure target =
        (Measure.add (Measure.smul head.2.toENNReal (Measure.dirac source head.1))
          ((FiniteMeasure.mk tail).toMeasure source)).bind kernel
      rw [toMeasure_add, toMeasure_scale, Measure.add_bind, Measure.smul_bind,
        Measure.dirac_bind, represents, induction]

/-- Evaluating the interpreted measure on a measurable set equals the embedded table integral. -/
theorem toMeasure_apply (space : Space alpha) (measure : FiniteMeasure alpha)
    {set : Set alpha} (measurable : space.Measurable set) :
    measure.toMeasure space set = (measure.integral (fun value =>
      if @decide (set value) (Classical.propDecidable _) then 1 else 0)).toENNReal := by
  classical
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (Measure.zero_apply _).trans NNRat.toENNReal_zero.symm
    | cons head tail induction =>
      rw [toMeasure_cons, Measure.add_apply_measurable _ _ measurable,
        Measure.smul_apply_measurable _ _ measurable, Measure.dirac_apply _ _ measurable, induction]
      change ENNReal.add (ENNReal.mul head.2.toENNReal
        (if set head.1 then ENNReal.one else ENNReal.zero)) _ =
        (head.2 * (if decide (set head.1) then (1 : NNRat) else 0) +
          (FiniteMeasure.mk tail).integral _).toENNReal
      rw [NNRat.toENNReal_add, NNRat.toENNReal_mul]
      by_cases member : set head.1 <;> simp only [member, if_true, if_false,
        decide_true, decide_false, Bool.false_eq_true, NNRat.toENNReal_one, NNRat.toENNReal_zero]

/-- Finite extensional equivalence implies equality of interpreted measures.
(Injectivity does not hold for arbitrary non-discrete spaces). -/
theorem toMeasure_eq_of_equivalent (space : Space alpha) {left right : FiniteMeasure alpha}
    (equal : left ≈ₘ right) : left.toMeasure space = right.toMeasure space := by
  apply Measure.ext
  intro set measurable
  rw [toMeasure_apply space left measurable, toMeasure_apply space right measurable,
    equal]

/-- Any finite table with nonzero total mass interprets as a normalizable measure. -/
theorem toMeasure_isNormalizable (space : Space alpha) (measure : FiniteMeasure alpha)
    (nonzero : measure.total ≠ 0) : Measure.IsNormalizable (measure.toMeasure space) where
  finite := measure.toMeasure_isFinite space
  nonzero := by
    rw [toMeasure_univ]
    intro zero
    exact nonzero ((NNRat.toENNReal_eq_zero_iff _).mp zero)

/-- Interpretation commutes with normalization between finite PMFs and continuous measures. -/
theorem toMeasure_normalize (space : Space alpha) (measure : FiniteMeasure alpha)
    (nonzero : measure.total ≠ 0) :
    (FinitePMF.normalize measure nonzero).measure.toMeasure space =
      Measure.normalize (measure.toMeasure space) (measure.toMeasure_isNormalizable space nonzero) := by
  symm
  apply Measure.normalize_eq_of_smul_eq
  change Measure.smul _ ((measure.scale (NNRat.inverse measure.total nonzero)).toMeasure space) = _
  rw [toMeasure_scale, toMeasure_univ, Measure.smul_smul, ← NNRat.toENNReal_mul,
    NNRat.mul_inverse_self, NNRat.toENNReal_one, Measure.one_smul]

end FiniteMeasure

end Foundations.Probability
