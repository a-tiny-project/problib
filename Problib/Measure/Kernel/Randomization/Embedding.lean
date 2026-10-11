module

public import Problib.Measure.Kernel.Randomization.Basic
public import Problib.Measure.Additive.Retraction

set_option autoImplicit false

namespace Problib.Measure.Kernel.Randomizer

universe u v w

public section

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {target : Space beta} {ambient : Space gamma}

/-- Transports an already supplied Uniform randomizer through a measurable embedding
and explicit fallback point back to the target space. -/
@[expose] noncomputable def ofEmbedding (kernel : Kernel source target)
    (embedding : MeasurableEmbedding target ambient) (fallback : beta)
    (encoded : Randomizer (kernel.map embedding.function embedding.measurable)) :
    Randomizer kernel := by
  have same : (kernel.map embedding.function embedding.measurable).map
      (embedding.retract fallback) (embedding.retract_measurable fallback) = kernel := by
    apply Kernel.ext
    intro input
    exact (kernel input).map_retract_map embedding fallback
  exact same ▸ encoded.map (embedding.retract fallback) (embedding.retract_measurable fallback)

end

end Problib.Measure.Kernel.Randomizer
