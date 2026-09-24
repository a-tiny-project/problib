module

public import Problib.Real.Extended
public import Problib.Countable.Bijection

set_option autoImplicit false

namespace Problib.Real.ENNReal

open scoped Rat

@[expose] public def rationalBasisRat (index : Nat) : Rat :=
  let pair := Countable.Pair.decode index
  (pair.1 : Int) /. ((pair.2 + 1 : Nat) : Int)

public theorem rationalBasisRat_nonnegative (index : Nat) :
    0 ≤ rationalBasisRat index := by
  unfold rationalBasisRat
  exact Rat.divInt_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

@[expose] public def rationalBasis (index : Nat) : ENNReal :=
  ofRat (rationalBasisRat index) (rationalBasisRat_nonnegative index)

public theorem rationalBasis_finite (index : Nat) :
    Finite (rationalBasis index) :=
  True.intro

public theorem exists_rationalBasis (value : Rat)
    (nonnegative : 0 ≤ value) :
    ∃ index, rationalBasis index = ofRat value nonnegative := by
  let pair : Nat × Nat := (value.num.toNat, value.den - 1)
  refine ⟨Countable.Pair.encode pair, ?_⟩
  have numerator : ((value.num.toNat : Nat) : Int) = value.num :=
    Int.toNat_of_nonneg (Rat.num_nonneg.mpr nonnegative)
  have denominator : value.den - 1 + 1 = value.den :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr value.den_nz)
  have rationalEqual :
      rationalBasisRat (Countable.Pair.encode pair) = value := by
    unfold rationalBasisRat
    rw [Countable.Pair.decode_encode]
    change
      (((value.num.toNat : Nat) : Int) /.
        ((value.den - 1 + 1 : Nat) : Int)) = value
    rw [numerator, denominator, Rat.num_divInt_den]
  unfold rationalBasis ofRat
  apply congrArg finite
  apply NNReal.ext
  exact congrArg Construction.Dedekind.selection.ofRat rationalEqual

public theorem exists_rationalBasis_between {left right : ENNReal}
    (less : lt left right) :
    ∃ index, lt left (rationalBasis index) ∧
      lt (rationalBasis index) right := by
  cases left with
  | top => exact False.elim (less.right (le_top right))
  | finite leftValue =>
      cases right with
      | finite rightValue =>
          rcases exists_rational_between_of_finite
              (left := finite leftValue) (right := finite rightValue)
              True.intro True.intro less with
            ⟨rational, nonnegative, leftRational, rationalRight⟩
          rcases exists_rationalBasis rational nonnegative with
            ⟨index, equal⟩
          exact ⟨index, equal ▸ leftRational, equal ▸ rationalRight⟩
      | top =>
          rcases Construction.Dedekind.exists_nat_strict_upper
              (NNReal.toReal leftValue) with
            ⟨natural, leftNatural⟩
          rcases exists_rationalBasis (natural : Rat)
              Rat.natCast_nonneg with ⟨index, equal⟩
          refine ⟨index, ?_, ?_⟩
          · rw [equal]
            exact leftNatural
          · exact ⟨le_top _, fun reverse =>
              finite_ne_top (NNReal.ofRat (natural : Rat) Rat.natCast_nonneg)
                (top_le_iff.mp reverse)⟩

@[expose] public noncomputable def approximation
    (value : ENNReal) : Nat → ENNReal
  | 0 => zero
  | index + 1 => by
      classical
      exact if included : le (rationalBasis index) value then
        if dominates : le (approximation value index)
            (rationalBasis index) then
          rationalBasis index
        else
          approximation value index
      else
        approximation value index

public theorem approximation_finite (value : ENNReal) (index : Nat) :
    Finite (approximation value index) := by
  induction index with
  | zero => exact True.intro
  | succ index induction =>
      rw [approximation]
      split
      · split
        · exact rationalBasis_finite index
        · exact induction
      · exact induction

public theorem approximation_step (value : ENNReal) (index : Nat) :
    le (approximation value index) (approximation value (index + 1)) := by
  classical
  by_cases included : le (rationalBasis index) value
  · by_cases dominates : le (approximation value index)
        (rationalBasis index)
    · simpa only [approximation, dif_pos included, dif_pos dominates]
        using dominates
    · simp only [approximation, dif_pos included, dif_neg dominates]
      exact le_refl _
  · simp only [approximation, dif_neg included]
    exact le_refl _

public theorem approximation_le (value : ENNReal) (index : Nat) :
    le (approximation value index) value := by
  induction index with
  | zero => exact zero_le value
  | succ index induction =>
      rw [approximation]
      split
      · split
        · assumption
        · exact induction
      · exact induction

public theorem basis_le_approximation_next {value : ENNReal} {index : Nat}
    (included : le (rationalBasis index) value) :
    le (rationalBasis index) (approximation value (index + 1)) := by
  classical
  simp only [approximation, dif_pos included]
  by_cases dominates : le (approximation value index)
      (rationalBasis index)
  · rw [dif_pos dominates]
    exact le_refl _
  · rw [dif_neg dominates]
    rcases le_total (approximation value index)
        (rationalBasis index) with forward | reverse
    · exact False.elim (dominates forward)
    · exact reverse

public theorem iSup_approximation (value : ENNReal) :
    iSup (approximation value) = value := by
  apply le_antisymm
  · apply iSup_le
    exact approximation_le value
  · apply Classical.byContradiction
    intro notIncluded
    have strict : lt (iSup (approximation value)) value :=
      ⟨iSup_le (approximation_le value), notIncluded⟩
    rcases exists_rationalBasis_between strict with
      ⟨index, supremumBasis, basisValue⟩
    have basisSupremum :
        le (rationalBasis index) (iSup (approximation value)) :=
      le_trans (basis_le_approximation_next basisValue.left)
        (le_iSup (approximation value) (index + 1))
    exact supremumBasis.right basisSupremum

end Problib.Real.ENNReal
