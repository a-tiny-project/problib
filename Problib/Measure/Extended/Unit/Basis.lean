module

public import Problib.Measure.Extended.Unit
public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

/-- Enumerate rational basis points in the unit interval by clamping extended
nonnegative rationals to one. -/
@[expose] public noncomputable def unitRationalBasis (index : Nat) : UnitInterval :=
  unitClamp (ENNReal.rationalBasis index)

/-- Between any two strictly ordered unit-interval points there exists an
indexed rational basis point. -/
public theorem exists_unitRationalBasis_between {left right : UnitInterval}
    (less : Dedekind.lt left.val right.val) :
    ∃ index, Dedekind.lt left.val (unitRationalBasis index).val ∧
      Dedekind.lt (unitRationalBasis index).val right.val := by
  have extendedLess := (ENNReal.ofReal_lt_ofReal_iff left.property.1 right.property.1).mpr less
  rcases ENNReal.exists_rationalBasis_between extendedLess with ⟨index, above, below⟩
  have bound : ENNReal.le (ENNReal.rationalBasis index) ENNReal.one :=
    ENNReal.le_trans below.1 ((ENNReal.ofReal_le_iff_le_toReal
      (upper := ENNReal.one) True.intro).mpr right.property.2)
  have recover : ENNReal.ofReal (unitRationalBasis index).val = ENNReal.rationalBasis index :=
    ofReal_unitClamp_of_le bound
  rw [← recover] at above below
  exact ⟨index,
    (ENNReal.ofReal_lt_ofReal_iff left.property.1 (unitRationalBasis index).property.1).mp above,
    (ENNReal.ofReal_lt_ofReal_iff (unitRationalBasis index).property.1 right.property.1).mp below⟩

end Problib.Measure.Real
