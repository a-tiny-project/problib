import Problib.Probability.Finite.Interpretation
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-! # Integrals against an interpreted table, row by row

An interpreted table is a finite sum of weighted Dirac measures, so the Lebesgue
integral of any measurable integrand against it is the weighted sum of the
integrand at the listed rows. The integrand has to agree with a rational weight
only at those rows, which is what a caller has when a kernel is known only where
the table puts mass.
-/

namespace Problib.Probability

open Problib.Measure Problib.Real

universe u v

namespace FiniteMeasure

variable {alpha : Type u} {beta : Type v}

/-- The Lebesgue integral against a table pushed along a map is the table's own
integral of a rational weight that agrees with the integrand at each listed row. -/
theorem lintegral_toMeasure_map {space : Space beta} (measure : FiniteMeasure alpha)
    (function : alpha → beta) {integrand : beta → ENNReal}
    (measurable : ENNRealMeasurable space integrand) (weight : alpha → NNRat)
    (agree : ∀ row ∈ measure.weights,
      integrand (function row.1) = (weight row.1).toENNReal) :
    lintegral ((measure.map function).toMeasure space) integrand =
      (measure.integral weight).toENNReal := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (lintegral_zero_measure _).trans NNRat.toENNReal_zero.symm
    | cons head tail induction =>
      cases head with
      | mk value mass =>
        change lintegral (Measure.add (Measure.smul mass.toENNReal
            (Measure.dirac space (function value)))
            (((FiniteMeasure.mk tail).map function).toMeasure space)) integrand =
          (mass * weight value + (FiniteMeasure.mk tail).integral weight).toENNReal
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac space _ measurable,
          agree (value, mass) (List.Mem.head _),
          induction (fun row member => agree row (List.Mem.tail _ member)),
          NNRat.toENNReal_add, NNRat.toENNReal_mul]

/-- The Lebesgue integral against an interpreted table is the table's own
integral of a rational weight that agrees with the integrand at each listed row. -/
theorem lintegral_toMeasure {space : Space alpha} (measure : FiniteMeasure alpha)
    {integrand : alpha → ENNReal} (measurable : ENNRealMeasurable space integrand)
    (weight : alpha → NNRat)
    (agree : ∀ row ∈ measure.weights, integrand row.1 = (weight row.1).toENNReal) :
    lintegral (measure.toMeasure space) integrand = (measure.integral weight).toENNReal := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (lintegral_zero_measure _).trans NNRat.toENNReal_zero.symm
    | cons head tail induction =>
      cases head with
      | mk value mass =>
        change lintegral (Measure.add (Measure.smul mass.toENNReal (Measure.dirac space value))
            ((FiniteMeasure.mk tail).toMeasure space)) integrand =
          (mass * weight value + (FiniteMeasure.mk tail).integral weight).toENNReal
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac space _ measurable,
          agree (value, mass) (List.Mem.head _),
          induction (fun row member => agree row (List.Mem.tail _ member)),
          NNRat.toENNReal_add, NNRat.toENNReal_mul]

/-- The Lebesgue integral of any integrand, measurable or not, against a table
pushed along a map is the table's own integral of a rational weight that agrees
with the integrand at each listed row, once every listed row lands on a
measurable point. -/
theorem lintegral_toMeasure_map_of_singleton {space : Space beta}
    (measure : FiniteMeasure alpha) (function : alpha → beta) (integrand : beta → ENNReal)
    (points : ∀ row ∈ measure.weights, space.Measurable (Set.singleton (function row.1)))
    (weight : alpha → NNRat)
    (agree : ∀ row ∈ measure.weights,
      integrand (function row.1) = (weight row.1).toENNReal) :
    lintegral ((measure.map function).toMeasure space) integrand =
      (measure.integral weight).toENNReal := by
  cases measure with
  | mk weights =>
    induction weights with
    | nil => exact (lintegral_zero_measure _).trans NNRat.toENNReal_zero.symm
    | cons head tail induction =>
      cases head with
      | mk value mass =>
        change lintegral (Measure.add (Measure.smul mass.toENNReal
            (Measure.dirac space (function value)))
            (((FiniteMeasure.mk tail).map function).toMeasure space)) integrand =
          (mass * weight value + (FiniteMeasure.mk tail).integral weight).toENNReal
        rw [lintegral_add_measure, lintegral_smul_measure,
          lintegral_dirac_of_measurable_singleton space _ _ (points (value, mass) (List.Mem.head _)),
          agree (value, mass) (List.Mem.head _),
          induction (fun row member => points row (List.Mem.tail _ member))
            (fun row member => agree row (List.Mem.tail _ member)),
          NNRat.toENNReal_add, NNRat.toENNReal_mul]

end FiniteMeasure

end Problib.Probability
