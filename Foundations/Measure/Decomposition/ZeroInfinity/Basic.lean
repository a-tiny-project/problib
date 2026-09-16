module

public import Foundations.Measure.Additive.Core

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u

namespace Measure

variable {alpha : Type u} {space : Space alpha}

/-- A measurable set on which every measurable subset has either zero or
infinite mass. -/
public structure IsZeroInfinitySet (measure : Measure space)
    (set : Set alpha) : Prop where
  measurable : space.Measurable set
  subsets_zero_or_top : ∀ {subset : Set alpha},
    space.Measurable subset →
    Set.Subset subset set →
    measure subset = ENNReal.zero ∨ measure subset = ENNReal.top

/-- A greatest zero-infinity set, unique modulo a null symmetric difference. -/
public structure TopZeroInfinitySet (measure : Measure space) : Type u where
  set : Set alpha
  zeroInfinity : IsZeroInfinitySet measure set
  greatest : ∀ {other : Set alpha},
    IsZeroInfinitySet measure other →
    measure (Set.difference other set) = ENNReal.zero

/-- Greatest zero-infinity sets agree modulo null sets. -/
public theorem TopZeroInfinitySet.equalModuloNull
    {measure : Measure space}
    (left right : TopZeroInfinitySet measure) :
    measure (Set.difference left.set right.set) = ENNReal.zero ∧
      measure (Set.difference right.set left.set) = ENNReal.zero :=
  ⟨right.greatest left.zeroInfinity,
    left.greatest right.zeroInfinity⟩

end Measure

end Foundations.Measure
