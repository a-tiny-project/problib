module

public import Problib.Measure.Kernel.Randomization.Unit
public import Problib.Measure.Kernel.Randomization.Embedding
public import Problib.Measure.StandardBorel.Basic

set_option autoImplicit false

namespace Problib.Measure.Kernel.Randomizer

open Problib.Measure.Real Problib.Real

universe u v

public section

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- Constructs a jointly measurable Uniform randomizer for any probability kernel
into a standard-Borel result space over an arbitrary measurable parameter space.
Handles empty result and parameter carriers without requiring a global inhabitant premise. -/
@[expose] noncomputable def ofStandardBorel (kernel : Kernel source target)
    (presentation : StandardBorel target)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) : Randomizer kernel := by
  classical
  by_cases inhabited : Nonempty beta
  · let encoded := kernel.map presentation.embedding.function presentation.embedding.measurable
    have probability : ∀ input, Measure.IsProbability (encoded input) :=
      fun input => (normalized input).map _ presentation.embedding.measurable
    exact ofEmbedding kernel presentation.embedding (Classical.choice inhabited)
      (ofUnitInterval encoded probability)
  · have impossible : ∀ input : alpha, False :=
      fun input => inhabited (normalized input).nonempty
    let function : alpha × UnitInterval → beta := fun pair => False.elim (impossible pair.1)
    have measurable : MeasurableMap (Space.product source unitBorel) target function := by
      intro region _
      have empty : Set.preimage function region = Set.empty := by
        apply Set.ext
        intro pair
        exact False.elim (impossible pair.1)
      rw [empty]
      exact (Space.product source unitBorel).empty
    exact ⟨function, measurable, fun input => False.elim (impossible input)⟩

/-- A kernel into a standard-Borel space admits a Uniform randomizer if and only if
every parameter fiber is a probability measure. -/
theorem nonempty_iff_probability (kernel : Kernel source target)
    (presentation : StandardBorel target) :
    Nonempty (Randomizer kernel) ↔ ∀ input, Measure.IsProbability (kernel input) :=
  ⟨fun ⟨selection⟩ => selection.isProbability,
    fun normalized => ⟨ofStandardBorel kernel presentation normalized⟩⟩

end

end Problib.Measure.Kernel.Randomizer
