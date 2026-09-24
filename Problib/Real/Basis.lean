module

public import Problib.Real.Construction.Dedekind.Selection
public import Problib.Countable.Bijection

set_option autoImplicit false

namespace Problib.Real.Construction.Dedekind

open scoped Rat

private def integerCode (index : Nat) : Int :=
  let pair := Countable.Pair.decode index
  (pair.1 : Int) - (pair.2 : Int)

private theorem integerCode_surjective (value : Int) :
    ∃ index, integerCode index = value := by
  cases value with
  | ofNat value =>
      refine ⟨Countable.Pair.encode (value, 0), ?_⟩
      simp only [integerCode, Countable.Pair.decode_encode]
      rfl
  | negSucc value =>
      refine ⟨Countable.Pair.encode (0, value + 1), ?_⟩
      simp only [integerCode, Countable.Pair.decode_encode]
      rfl

private def rationalCode (index : Nat) : Rat :=
  let pair := Countable.Pair.decode index
  integerCode pair.1 /. ((pair.2 + 1 : Nat) : Int)

private theorem rationalCode_surjective (value : Rat) :
    ∃ index, rationalCode index = value := by
  rcases integerCode_surjective value.num with ⟨numerator, numeratorEqual⟩
  refine ⟨Countable.Pair.encode (numerator, value.den - 1), ?_⟩
  have denominator : value.den - 1 + 1 = value.den :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr value.den_nz)
  simp only [rationalCode, Countable.Pair.decode_encode, numeratorEqual, denominator,
    Rat.num_divInt_den]

/-- Countable rational basis elements inside the selected Dedekind real carrier. -/
public noncomputable def rationalBasis (index : Nat) : selection.Carrier :=
  selection.ofRat (rationalCode index)

/-- Every rational embedded into the selected Dedekind carrier appears in the rational basis. -/
public theorem exists_rationalBasis (value : Rat) :
    ∃ index, rationalBasis index = selection.ofRat value := by
  rcases rationalCode_surjective value with ⟨index, equal⟩
  exact ⟨index, congrArg selection.ofRat equal⟩

/-- Any two strictly ordered real numbers admit an intervening rational basis element. -/
public theorem exists_rationalBasis_between {left right : selection.Carrier}
    (less : lt left right) :
    ∃ index, lt left (rationalBasis index) ∧ lt (rationalBasis index) right := by
  rcases exists_rational_between less with ⟨rational, lower, upper⟩
  rcases exists_rationalBasis rational with ⟨index, equal⟩
  exact ⟨index, equal ▸ lower, equal ▸ upper⟩

end Problib.Real.Construction.Dedekind
