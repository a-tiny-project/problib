module

public import Foundations.Real.Construction.Dedekind.Selection
public import Foundations.Real.Series.Bijection

set_option autoImplicit false

namespace Foundations.Real.Construction.Dedekind

open scoped Rat

private def integerCode (index : Nat) : Int :=
  let pair := NatProductBijection.decode index
  (pair.1 : Int) - (pair.2 : Int)

private theorem integerCode_surjective (value : Int) :
    ∃ index, integerCode index = value := by
  cases value with
  | ofNat value =>
      refine ⟨NatProductBijection.encode (value, 0), ?_⟩
      simp only [integerCode, NatProductBijection.decodeEncode]
      rfl
  | negSucc value =>
      refine ⟨NatProductBijection.encode (0, value + 1), ?_⟩
      simp only [integerCode, NatProductBijection.decodeEncode]
      rfl

private def rationalCode (index : Nat) : Rat :=
  let pair := NatProductBijection.decode index
  integerCode pair.1 /. ((pair.2 + 1 : Nat) : Int)

private theorem rationalCode_surjective (value : Rat) :
    ∃ index, rationalCode index = value := by
  rcases integerCode_surjective value.num with ⟨numerator, numeratorEqual⟩
  refine ⟨NatProductBijection.encode (numerator, value.den - 1), ?_⟩
  have denominator : value.den - 1 + 1 = value.den :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr value.den_nz)
  simp only [rationalCode, NatProductBijection.decodeEncode, numeratorEqual, denominator,
    Rat.num_divInt_den]

/-- Countable rational basis elements inside the selected Dedekind real carrier. -/
public noncomputable def rationalBasis (index : Nat) : selection.Carrier :=
  selection.ofRat (rationalCode index)

/-- Every rational embedded into the selected Dedekind carrier appears in the rational basis. -/
public theorem existsRationalBasis (value : Rat) :
    ∃ index, rationalBasis index = selection.ofRat value := by
  rcases rationalCode_surjective value with ⟨index, equal⟩
  exact ⟨index, congrArg selection.ofRat equal⟩

/-- Any two strictly ordered real numbers admit an intervening rational basis element. -/
public theorem existsRationalBasisBetween {left right : selection.Carrier}
    (less : lt left right) :
    ∃ index, lt left (rationalBasis index) ∧ lt (rationalBasis index) right := by
  rcases existsRationalBetween less with ⟨rational, lower, upper⟩
  rcases existsRationalBasis rational with ⟨index, equal⟩
  exact ⟨index, equal ▸ lower, equal ▸ upper⟩

end Foundations.Real.Construction.Dedekind
