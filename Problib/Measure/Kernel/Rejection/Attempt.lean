module

public import Problib.Measure.Kernel.Comap
public import Problib.Measure.Embedding.Sum

set_option autoImplicit false

/-!
# Accepted and rejected parts of an attempt

An attempt is a kernel into `Unit ⊕ β`: the left summand is a rejection and
the right summand an accepted value. Its accepted part is the kernel it gives
the accepted values, and its rejection mass is the mass it gives the
rejection. A retry over the attempt scales its continuation by that mass.
-/

namespace Problib.Measure.Kernel

public section

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- The kernel an attempt gives its accepted values. -/
@[expose] noncomputable def accepted
    (attempt : Kernel source (Space.sum (Space.discrete Unit) target)) : Kernel source target :=
  attempt.comap (MeasurableEmbedding.inr (Space.discrete Unit) target)

/-- The mass an attempt gives its rejection at each input. -/
@[expose] noncomputable def rejection
    (attempt : Kernel source (Space.sum (Space.discrete Unit) target)) (input : alpha) :
    ENNReal :=
  attempt.comap (MeasurableEmbedding.inl (Space.discrete Unit) target) input Set.univ

/-- The rejection mass is measurable in the input. -/
theorem rejection_measurable
    (attempt : Kernel source (Space.sum (Space.discrete Unit) target)) :
    ENNRealMeasurable source (rejection attempt) :=
  (attempt.comap (MeasurableEmbedding.inl (Space.discrete Unit) target)).measurable
    (Space.discrete Unit).univ

end

end Problib.Measure.Kernel
