module

public import Problib.Measure.Kernel.Composition.Bind
import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-!
# Mass deficits add under bind

A sub-probability measure has deficit at most `ε` when its total mass is at
least `1 - ε`, stated without subtraction as `1 ≤ μ univ + ε`. Binding such a
measure with a kernel whose every fiber has deficit at most `δ` loses at most
`ε + δ`. A program that runs one bounded search after another therefore fails
with probability at most the sum of the searches' failure bounds.
-/
namespace Problib.Measure

open Problib.Real

public section

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

namespace Measure

/-- Binding a sub-probability measure with deficit at most `measureDeficit`
against a kernel whose every fiber has deficit at most `fiberDeficit` gives a
measure with deficit at most their sum. The fiber deficit is paid once per unit
of source mass, so the bound needs the source to be a sub-probability. -/
theorem bind_deficit_le {measure : Measure source} {kernel : Kernel source target}
    {measureDeficit fiberDeficit : ENNReal}
    (subProbability : ENNReal.le (measure Set.univ) ENNReal.one)
    (measureBound : ENNReal.le ENNReal.one (ENNReal.add (measure Set.univ) measureDeficit))
    (fiberBound : ∀ input,
      ENNReal.le ENNReal.one (ENNReal.add (kernel input Set.univ) fiberDeficit)) :
    ENNReal.le ENNReal.one
      (ENNReal.add (measure.bind kernel Set.univ) (ENNReal.add measureDeficit fiberDeficit)) := by
  rw [bind_apply _ _ target.univ]
  have covered : ENNReal.le (measure Set.univ)
      (ENNReal.add (lintegral measure fun input => kernel input Set.univ)
        (ENNReal.mul fiberDeficit (measure Set.univ))) := by
    have mono := lintegral_mono measure fiberBound
    rwa [lintegral_const, ENNReal.one_mul,
      lintegral_add measure (kernel.measurable target.univ)
        (ENNRealMeasurable.constant source fiberDeficit),
      lintegral_const] at mono
  have paid : ENNReal.le (ENNReal.mul fiberDeficit (measure Set.univ)) fiberDeficit := by
    have scaled := ENNReal.mul_le_mul_left subProbability fiberDeficit
    rwa [ENNReal.mul_one] at scaled
  refine ENNReal.le_trans measureBound ?_
  refine ENNReal.le_trans (ENNReal.add_le_add_right
    (ENNReal.le_trans covered (ENNReal.add_le_add_left paid _)) measureDeficit) ?_
  rw [ENNReal.add_assoc, ENNReal.add_comm fiberDeficit measureDeficit]
  exact ENNReal.le_refl _

end Measure

end

end Problib.Measure
