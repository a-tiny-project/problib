module

public import Foundations.Measure.Extended.Unit
public import Foundations.Real.Series.Basis

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

/-- Enumerate rational basis points in the unit interval by clamping extended
nonnegative rationals to one. -/
@[expose] public noncomputable def unitRationalBasis (index : Nat) : UnitInterval :=
  unitClamp (ENNReal.rationalBasis index)

/-- Between any two strictly ordered unit-interval points there exists an
indexed rational basis point. -/
public theorem existsUnitRationalBasisBetween {left right : UnitInterval}
    (less : Dedekind.lt left.val right.val) :
    ∃ index, Dedekind.lt left.val (unitRationalBasis index).val ∧
      Dedekind.lt (unitRationalBasis index).val right.val := by
  have extendedLess := (ENNReal.ofRealLtOfRealIff left.property.1 right.property.1).mpr less
  rcases ENNReal.existsRationalBasisBetween extendedLess with ⟨index, above, below⟩
  have bound : ENNReal.le (ENNReal.rationalBasis index) ENNReal.one :=
    ENNReal.leTrans below.1 ((ENNReal.ofRealLeIffLeToReal
      (upper := ENNReal.one) True.intro).mpr right.property.2)
  have recover : ENNReal.ofReal (unitRationalBasis index).val = ENNReal.rationalBasis index :=
    ofReal_unitClamp_of_le bound
  rw [← recover] at above below
  exact ⟨index,
    (ENNReal.ofRealLtOfRealIff left.property.1 (unitRationalBasis index).property.1).mp above,
    (ENNReal.ofRealLtOfRealIff (unitRationalBasis index).property.1 right.property.1).mp below⟩

end Foundations.Measure.Real
