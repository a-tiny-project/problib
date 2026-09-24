module

public import Problib.QuasiBorel.Measurable.Sum
public import Problib.Measure.Real.Borel

set_option autoImplicit false

/-!
# Partial random generators for s-finite quasi-Borel spaces

This module defines the shared partial random generator structure.
Generators map the real Borel random source into a target space extended with
a failure point, without measure-theoretic dependencies beyond the source.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure.Real (Carrier borel)

/-- The canonical real Borel random source for s-finite quasi-Borel spaces. -/
abbrev realSource := Source.ofMeasurable borel

/-- Extends a quasi-Borel space with an isolated failure point through a binary coproduct. -/
@[expose] def withFailure (space : Space realSource) : Space realSource :=
  Space.sum (Space.terminal realSource) space

/-- An accepted partial random map from the real Borel line into a failure-extended space. -/
structure Generator (space : Space realSource) where
  /-- Concrete random map into the failure-extended carrier. -/
  random : Carrier → (withFailure space).Carrier
  /-- Witness that the random map is an accepted quasi-Borel random element. -/
  accepted : (withFailure space).Random random

end

end Problib.QuasiBorel.SFinite
