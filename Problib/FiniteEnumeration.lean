module

public import Problib.Relation.List

set_option autoImplicit false

namespace Problib

public section

universe u

/-- A list containing every inhabitant of a carrier exactly once. -/
structure FiniteEnumeration {α : Type u} (values : List α) : Prop where
  nodup : values.Nodup
  complete : ∀ value, value ∈ values

namespace FiniteEnumeration

/-- The canonical enumeration of a finite index carrier. -/
theorem finRange (size : Nat) : FiniteEnumeration (List.finRange size) :=
  ⟨Relation.List.finRange_nodup size, fun value => List.mem_finRange value⟩

end FiniteEnumeration

end
end Problib
