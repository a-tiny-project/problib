import Problib.Measure.Giry.StandardBorel
import Problib.QuasiBorel.Probability.StandardBorel

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability.StandardBorel

open Problib.Measure hiding Space
open Problib.Measure.Real (borel)

universe u

variable {alpha : Type u} {source : Problib.Measure.Space alpha}

/-- The canonical map from the quasi-Borel probability object to the Giry law
space is measurable on induced spaces. -/
theorem toGiry_measurable (presentation : Problib.Measure.StandardBorel source) :
    MeasurableMap (object (Space.ofMeasurable borel source)).toMeasurable (Giry.space source)
      (toGiry presentation) := by
  apply Space.measurableMap_iff_random.mpr
  intro random accepted
  exact (toGiryHom presentation).map_random accepted

/-- The inverse map from the Giry law space to the quasi-Borel probability
object is measurable on induced spaces. -/
theorem ofGiry_measurable (presentation : Problib.Measure.StandardBorel source) :
    MeasurableMap (Giry.space source) (object (Space.ofMeasurable borel source)).toMeasurable
      (ofGiry presentation) := by
  intro region accepted
  have pulled : (Space.ofMeasurable borel (Giry.space source)).toMeasurable.Measurable
      (Set.preimage (ofGiry presentation) region) :=
    (ofGiryHom presentation).toMeasurable accepted
  rw [Space.toMeasurable_of_standardBorel_real (Giry.standardBorel presentation)] at pulled
  exact pulled

/-- Measurable-space equivalence between the induced measurable space of the
quasi-Borel probability object and the Giry probability law space for any
standard-Borel space (Heunen et al. (2017) Proposition 22(4)). -/
noncomputable def measurableEquivalence (presentation : Problib.Measure.StandardBorel source) :
    MeasurableEquivalence (object (Space.ofMeasurable borel source)).toMeasurable (Giry.space source) where
  forward := toGiry presentation
  inverse := ofGiry presentation
  inverse_forward := ofGiry_toGiry presentation
  forward_inverse := toGiry_ofGiry presentation
  forward_measurable := toGiry_measurable presentation
  inverse_measurable := ofGiry_measurable presentation

/-- Standard-Borel presentation of the induced measurable space of the
quasi-Borel probability object over a standard-Borel space. -/
noncomputable def induced_standardBorel (presentation : Problib.Measure.StandardBorel source) :
    Problib.Measure.StandardBorel (object (Space.ofMeasurable borel source)).toMeasurable :=
  Problib.Measure.StandardBorel.ofEmbedding (measurableEquivalence presentation).toEmbedding
    (Giry.standardBorel presentation)

end Problib.QuasiBorel.Probability.StandardBorel
