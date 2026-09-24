module

public import Problib.Measure.StandardBorel.Basic
public import Problib.Measure.Embedding.Generator
public import Problib.Measure.Real.Generator

set_option autoImplicit false

/-!
# Countable generators for standard-Borel spaces

Constructs a countable generator for any standard-Borel space by pulling back
the standard countable generator on ℝ along the measurable embedding.
-/

namespace Problib.Measure.StandardBorel

universe u

variable {α : Type u} {space : Space α}

/-- Canonical countable generator for a standard-Borel space, constructed by pullback
of the countable generator on the real line along the presentation embedding. -/
public noncomputable def countableGenerator (presentation : StandardBorel space) :
    Space.CountableGenerator space :=
  presentation.embeddingReal.countableGenerator Real.countableGenerator

end Problib.Measure.StandardBorel
