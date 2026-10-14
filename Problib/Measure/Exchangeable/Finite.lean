module

public import Problib.Measure.Exchangeable.Sampled
public import Problib.Measure.Additive.Dirac
public import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-!
# Urns with finitely many outcomes

At each valid statistic the draw kernel of a finite urn is a finite mixture of
point masses: a list of distinct outcomes, each weighted by the kernel's mass
at it. The consumers that split a draw over its outcomes are stated against
this structure.
-/

namespace Problib.Measure.Exchangeable

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- The draw kernel at each valid statistic is a finite mixture of point masses
at distinct, measurable outcomes. -/
structure Urn.Finite (U : Urn.{u, v} Y) (S : U.Sampled) where
  slots : U.Stat → List α
  nodup : ∀ s, (slots s).Nodup
  singleton : ∀ a, Y.Measurable (· = a)
  decomp : ∀ {s}, S.Valid s → S.kernel s =
    Measure.listSum ((slots s).map fun a => Measure.smul (S.kernel s (· = a)) (Measure.dirac Y a))

end

end Problib.Measure.Exchangeable
