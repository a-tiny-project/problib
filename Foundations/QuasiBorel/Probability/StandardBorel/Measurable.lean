import Foundations.Measure.Giry.StandardBorel
import Foundations.QuasiBorel.Probability.StandardBorel

set_option autoImplicit false

namespace Foundations.QuasiBorel.Probability.StandardBorel

open Foundations.Measure hiding Space
open Foundations.Measure.Real (borel)

universe u

variable {alpha : Type u} {source : Foundations.Measure.Space alpha}

/-- The canonical map from the quasi-Borel probability object to the Giry law
space is measurable on induced spaces. -/
theorem toGiry_measurable (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableMap (object (Space.ofMeasurable borel source)).toMeasurable (Giry.space source)
      (toGiry presentation) := by
  apply Space.measurableMap_iff_random.mpr
  intro random accepted
  exact (toGiryHom presentation).mapRandom accepted

/-- The inverse map from the Giry law space to the quasi-Borel probability
object is measurable on induced spaces. -/
theorem ofGiry_measurable (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableMap (Giry.space source) (object (Space.ofMeasurable borel source)).toMeasurable
      (ofGiry presentation) := by
  intro region accepted
  have pulled : (Space.ofMeasurable borel (Giry.space source)).toMeasurable.Measurable
      (Set.preimage (ofGiry presentation) region) :=
    (ofGiryHom presentation).toMeasurable accepted
  rw [Space.toMeasurable_ofStandardBorelReal (Giry.standardBorel presentation)] at pulled
  exact pulled

/-- Measurable-space equivalence between the induced measurable space of the
quasi-Borel probability object and the Giry probability law space for any
standard-Borel space (Heunen et al. (2017) Proposition 22(4)). -/
noncomputable def measurableEquivalence (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableEquivalence (object (Space.ofMeasurable borel source)).toMeasurable (Giry.space source) where
  forward := toGiry presentation
  inverse := ofGiry presentation
  inverse_forward := ofGiry_toGiry presentation
  forward_inverse := toGiry_ofGiry presentation
  forward_measurable := toGiry_measurable presentation
  inverse_measurable := ofGiry_measurable presentation

/-- Standard-Borel presentation of the induced measurable space of the
quasi-Borel probability object over a standard-Borel space. -/
noncomputable def induced_standardBorel (presentation : Foundations.Measure.StandardBorel source) :
    Foundations.Measure.StandardBorel (object (Space.ofMeasurable borel source)).toMeasurable :=
  Foundations.Measure.StandardBorel.ofEmbedding (measurableEquivalence presentation).toEmbedding
    (Giry.standardBorel presentation)

end Foundations.QuasiBorel.Probability.StandardBorel
