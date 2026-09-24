module

public import Problib.Analysis.Real.SignedSeries
public import Problib.Real.Series.Reindex

/-! Finite `ENNReal.tsum` agrees with the real limit of nonnegative partial sums. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind
open Problib.Real

noncomputable section

public theorem partial_sum_ofReal {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index)) (count : Nat) :
    ENNReal.partialSum (fun index => ENNReal.ofReal (values index)) count =
      ENNReal.ofReal (partialSum values count) := by
  induction count with
  | zero =>
      rw [ENNReal.partialSum, partial_sum_zero, ENNReal.ofReal_zero]
  | succ count induction =>
      rw [ENNReal.partialSum, partial_sum_succ, induction,
        ENNReal.ofReal_add (partial_sum_nonnegative nonnegative count)
          (nonnegative count)]

/-- A bounded nonnegative real series has a finite extended sum. -/
public theorem finite_tsum_of_bounded {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    {upper : selection.Carrier}
    (bounded : ∀ count, le (partialSum values count) upper) :
    ENNReal.Finite (ENNReal.tsum (fun index => ENNReal.ofReal (values index))) := by
  have upperBound : ENNReal.le
      (ENNReal.tsum (fun index => ENNReal.ofReal (values index)))
      (ENNReal.ofReal upper) := by
    apply ENNReal.tsum_le
    intro count
    rw [partial_sum_ofReal nonnegative]
    exact ENNReal.ofReal_monotone (bounded count)
  exact ENNReal.finite_of_le upperBound (ENNReal.ofReal_finite upper)

/-- A finite extended sum supplies the Dedekind least upper bound, hence the
ordinary limit, of its nonnegative real partial sums. -/
public theorem nonnegative_converges_to_tsum {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    (finite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (values index)))) :
    ConvergesTo (partialSum values)
      (ENNReal.toReal (ENNReal.tsum
        (fun index => ENNReal.ofReal (values index)))) := by
  let total := ENNReal.tsum (fun index => ENNReal.ofReal (values index))
  have totalFinite : ENNReal.Finite total := finite
  have totalUpper : Problib.Real.IsUpperBound le
      (fun value => ∃ count, partialSum values count = value)
      (ENNReal.toReal total) := by
    intro value member
    rcases member with ⟨count, equal⟩
    subst value
    have included := ENNReal.partialSum_le_tsum
      (fun index => ENNReal.ofReal (values index)) count
    rw [partial_sum_ofReal nonnegative] at included
    exact (ENNReal.ofReal_le_iff_le_toReal totalFinite).mp included
  have totalLeast : ∀ candidate : selection.Carrier,
      Problib.Real.IsUpperBound le
        (fun value => ∃ count, partialSum values count = value) candidate →
      le (ENNReal.toReal total) candidate := by
    intro candidate candidateUpper
    have candidateNonnegative : le zero candidate := by
      have atZero := candidateUpper (partialSum values 0) ⟨0, rfl⟩
      rwa [partial_sum_zero] at atZero
    have converted : ENNReal.le total (ENNReal.ofReal candidate) := by
      apply ENNReal.tsum_le
      intro count
      rw [partial_sum_ofReal nonnegative]
      exact ENNReal.ofReal_monotone
        (candidateUpper (partialSum values count) ⟨count, rfl⟩)
    have realBound :=
      (ENNReal.toReal_le_toReal_iff totalFinite
        (ENNReal.ofReal_finite candidate)).mpr converted
    rw [ENNReal.toReal_ofReal candidateNonnegative] at realBound
    exact realBound
  exact monotone_converges_to_lub (partialSum values)
    (fun _ _ included => partial_sum_monotone nonnegative included)
    totalUpper totalLeast

public theorem nonnegative_converges_to_tsum_of_bounded
    {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    {upper : selection.Carrier}
    (bounded : ∀ count, le (partialSum values count) upper) :
    ConvergesTo (partialSum values)
      (ENNReal.toReal (ENNReal.tsum
        (fun index => ENNReal.ofReal (values index)))) :=
  nonnegative_converges_to_tsum nonnegative
    (finite_tsum_of_bounded nonnegative bounded)

/-- A signed series is the difference of its finite positive and negative
extended sums. -/
public theorem converges_to_parts {values : Nat → selection.Carrier}
    (positiveFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (positivePart (values index)))))
    (negativeFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (negativePart (values index))))) :
    ConvergesTo (partialSum values)
      (sub
        (ENNReal.toReal (ENNReal.tsum
          (fun index => ENNReal.ofReal (positivePart (values index)))))
        (ENNReal.toReal (ENNReal.tsum
          (fun index => ENNReal.ofReal (negativePart (values index)))))) := by
  have positiveLimit := nonnegative_converges_to_tsum
    (fun index => positive_part_nonnegative (values index)) positiveFinite
  have negativeLimit := nonnegative_converges_to_tsum
    (fun index => negative_part_nonnegative (values index)) negativeFinite
  have combined := converges_to_sub positiveLimit negativeLimit
  have equal :
      (fun count => sub
        (partialSum (fun index => positivePart (values index)) count)
        (partialSum (fun index => negativePart (values index)) count)) =
      partialSum values := by
    funext count
    rw [← partial_sum_sub]
    apply congrArg (fun series => partialSum series count)
    funext index
    exact positive_sub_negative (values index)
  rw [equal] at combined
  exact combined

public theorem summable_of_finite_parts {values : Nat → selection.Carrier}
    (positiveFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (positivePart (values index)))))
    (negativeFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (negativePart (values index))))) :
    Summable values :=
  ⟨_, converges_to_parts positiveFinite negativeFinite⟩

public theorem sum_eq_parts {values : Nat → selection.Carrier}
    (certificate : Summable values)
    (positiveFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (positivePart (values index)))))
    (negativeFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (negativePart (values index))))) :
    sum values certificate =
      sub
        (ENNReal.toReal (ENNReal.tsum
          (fun index => ENNReal.ofReal (positivePart (values index)))))
        (ENNReal.toReal (ENNReal.tsum
          (fun index => ENNReal.ofReal (negativePart (values index))))) :=
  sum_eq_of_converges values certificate
    (converges_to_parts positiveFinite negativeFinite)

public theorem parts_finite_of_absolute {values : Nat → selection.Carrier}
    (absolute : AbsolutelySummable values) :
    ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (positivePart (values index)))) ∧
    ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal (negativePart (values index)))) := by
  rcases absolute with ⟨upper, bounded⟩
  constructor
  · apply finite_tsum_of_bounded
      (fun index => positive_part_nonnegative (values index))
    intro count
    exact le_trans
      (partial_sum_le
        (fun index => positive_part_le_abs (values index)) count)
      (bounded count)
  · apply finite_tsum_of_bounded
      (fun index => negative_part_nonnegative (values index))
    intro count
    exact le_trans
      (partial_sum_le
        (fun index => negative_part_le_abs (values index)) count)
      (bounded count)

/-- Absolute summability survives any bijective enumeration of its terms. -/
public theorem absolutely_summable_reindex
    {values : Nat → selection.Carrier}
    (equivalence : Problib.Countable.Bijection Nat Nat)
    (absolute : AbsolutelySummable values) :
    AbsolutelySummable (fun index => values (equivalence.forward index)) := by
  rcases absolute with ⟨upper, bounded⟩
  have originalFinite := finite_tsum_of_bounded
    (fun index => abs_nonnegative (values index)) bounded
  have reindexEqual := ENNReal.tsum_reindex equivalence
    (fun index => ENNReal.ofReal (abs (values index)))
  have reindexedFinite : ENNReal.Finite (ENNReal.tsum
      (fun index => ENNReal.ofReal
        (abs (values (equivalence.forward index))))) := by
    rw [reindexEqual]
    exact originalFinite
  refine ⟨ENNReal.toReal (ENNReal.tsum
    (fun index => ENNReal.ofReal
      (abs (values (equivalence.forward index))))), fun count => ?_⟩
  have included := ENNReal.partialSum_le_tsum
    (fun index => ENNReal.ofReal
      (abs (values (equivalence.forward index)))) count
  rw [partial_sum_ofReal
    (fun index => abs_nonnegative (values (equivalence.forward index)))] at included
  exact (ENNReal.ofReal_le_iff_le_toReal reindexedFinite).mp included

/-- Absolute rearrangement preserves the real sum, with each convergence
certificate kept explicit. -/
public theorem sum_reindex_absolute {values : Nat → selection.Carrier}
    (equivalence : Problib.Countable.Bijection Nat Nat)
    (absolute : AbsolutelySummable values)
    (original : Summable values)
    (reordered : Summable
      (fun index => values (equivalence.forward index))) :
    sum (fun index => values (equivalence.forward index)) reordered =
      sum values original := by
  have originalParts := parts_finite_of_absolute absolute
  have reorderedParts := parts_finite_of_absolute
    (absolutely_summable_reindex equivalence absolute)
  rw [sum_eq_parts reordered reorderedParts.left reorderedParts.right,
    sum_eq_parts original originalParts.left originalParts.right]
  have positiveEqual := ENNReal.tsum_reindex equivalence
    (fun index => ENNReal.ofReal (positivePart (values index)))
  have negativeEqual := ENNReal.tsum_reindex equivalence
    (fun index => ENNReal.ofReal (negativePart (values index)))
  rw [positiveEqual, negativeEqual]

end

end Problib.Analysis.Real.SignedSeries
