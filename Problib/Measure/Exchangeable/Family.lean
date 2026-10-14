module

public import Problib.Measure.Kernel.Basic

set_option autoImplicit false

/-!
# Law families

A law family is a Markov kernel: a probability law on its target at every
state.
-/

namespace Problib.Measure.Exchangeable

public section

universe u v

variable {σ : Type u} {τ : Type v}

/-- A probability law on `target` at every state. -/
structure LawFamily (state : Space σ) (target : Space τ) where
  kernel : Kernel state target
  markov : ∀ s, Measure.IsProbability (kernel s)

end

end Problib.Measure.Exchangeable
