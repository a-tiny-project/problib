module

public import Problib.Analysis.Gaussian.Network.Reverse
import Problib.Real.Grind

/-! A three-node network, reversed at each adjacent pair.

The network is `x₀ ~ N(1, 2)`, `x₁ ~ N(0, 1)` with a zero coefficient on `x₀`,
and `x₂ ~ N(1 + 2 x₀ + 3 x₁, 1)`. Its mean is `(1, 0, 3)` and its covariance is
`[[2, 0, 4], [0, 1, 3], [4, 3, 18]]` (`mean_closed`, `covariance_closed`).

Reversing at `0` has slope zero, so the gain is zero and the rebuilt rows only
trade places (`reverseAt_zero_rows`). Reversing at `1` has slope three, and
`x₂` reads `x₀` where `x₁` did not, so the rebuilt row for `x₁` gains a
coefficient on `x₀`: the fill-in (`reverseAt_one_rows`). In both cases the
reversed network's own recurrences give the swapped mean and covariance as
closed forms (`reverseAt_zero_moments`, `reverseAt_one_moments`). The law
pushed along each swap has those moments as certified integrals
(`swapped_moments`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian.NetworkExample

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Gaussian

noncomputable section

/-- `x₀ ~ N(1, 2)`, `x₁ ~ N(0 · x₀, 1)`, `x₂ ~ N(1 + 2 x₀ + 3 x₁, 1)`. -/
@[expose] public def rows : List Row :=
  [⟨one, [], selection.ofRat 2⟩, ⟨zero, [zero], one⟩,
    ⟨one, [selection.ofRat 2, selection.ofRat 3], one⟩]

@[expose] public def network : Network where
  rows := rows
  triangular := by
    intro position row found
    match position, found with
    | 0, found => cases Option.some.inj found; rfl
    | 1, found => cases Option.some.inj found; rfl
    | 2, found => cases Option.some.inj found; rfl
    | _ + 3, found => cases found
  positive := by
    intro row member
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ofRat_two_positive
    · exact one_positive
    · exact one_positive

public theorem mean_closed :
    network.mean = [one, zero, selection.ofRat 3] := by
  simp only [Network.mean, network, rows, List.foldl, meanAppend, dot, List.nil_append,
    List.cons_append, List.cons.injEq, and_true]
  and_intros <;> real_grind

public theorem covariance_closed :
    network.covariance =
      [[selection.ofRat 2, zero, selection.ofRat 4], [zero, one, selection.ofRat 3],
        [selection.ofRat 4, selection.ofRat 3, selection.ofRat 18]] := by
  simp only [Network.covariance, network, rows, List.foldl, covarianceAppend, dot, List.map,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  and_intros <;> real_grind

/-! ### Reversing at `0`: slope zero -/

/-- With slope zero the gain is zero: the two rebuilt rows trade places and
the later row reads its two parents in swapped columns. -/
public theorem reverseAt_zero_rows :
    (network.reverseAt 0).intercept = [zero, one, one] ∧
      (network.reverseAt 0).coefficients = [[], [zero], [selection.ofRat 3, selection.ofRat 2]] ∧
      (network.reverseAt 0).variance = [one, selection.ofRat 2, one] := by
  simp only [Network.intercept, Network.coefficients, Network.variance, Network.reverseAt, network,
    rows, reverseRows, List.drop, List.take, reverseFirst, reverseSecond, Row.swapColumns,
    pairSlope, pairGain, pairVariance, combine, entry, swapAt, List.map, List.zipWith,
    List.getD_cons_zero, List.nil_append, List.cons.injEq, and_true]
  and_intros <;> real_grind

public theorem reverseAt_zero_moments :
    (network.reverseAt 0).mean = [zero, one, selection.ofRat 3] ∧
      swapAt 0 network.mean = [zero, one, selection.ofRat 3] ∧
      (network.reverseAt 0).covariance =
        [[one, zero, selection.ofRat 3], [zero, selection.ofRat 2, selection.ofRat 4],
          [selection.ofRat 3, selection.ofRat 4, selection.ofRat 18]] ∧
      swapMatrixAt 0 network.covariance =
        [[one, zero, selection.ofRat 3], [zero, selection.ofRat 2, selection.ofRat 4],
          [selection.ofRat 3, selection.ofRat 4, selection.ofRat 18]] := by
  refine ⟨?_, by rw [mean_closed]; rfl, ?_, by rw [covariance_closed]; rfl⟩
  · simp only [Network.mean, Network.reverseAt, network, rows, reverseRows, List.drop, List.take,
      reverseFirst, reverseSecond, Row.swapColumns, pairSlope, pairGain, pairVariance, combine,
      entry, swapAt, List.map, List.zipWith, List.getD_cons_zero, List.foldl, meanAppend, dot,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    and_intros <;> real_grind
  · simp only [Network.covariance, Network.reverseAt, network, rows, reverseRows, List.drop,
      List.take, reverseFirst, reverseSecond, Row.swapColumns, pairSlope, pairGain, pairVariance,
      combine, entry, swapAt, List.map, List.zipWith, List.getD_cons_zero, List.foldl,
      covarianceAppend, dot, List.nil_append, List.cons_append, List.cons.injEq, and_true]
    and_intros <;> real_grind

/-! ### Reversing at `1`: slope three, with fill-in -/

/-- With slope three the old `x₂` becomes node `1` with variance `1 + 3² = 10`,
and the old `x₁` becomes node `2` with gain `3/10` and variance `1/10`. The old
`x₁` did not read `x₀`, but its rebuilt row does, with coefficient `-3/5`: the
fill-in. -/
public theorem reverseAt_one_rows :
    (network.reverseAt 1).intercept =
        [one, one, neg (div (selection.ofRat 3) (selection.ofRat 10))] ∧
      (network.reverseAt 1).coefficients =
        [[], [selection.ofRat 2], [neg (div (selection.ofRat 3) (selection.ofRat 5)),
          div (selection.ofRat 3) (selection.ofRat 10)]] ∧
      (network.reverseAt 1).variance =
        [selection.ofRat 2, selection.ofRat 10, div one (selection.ofRat 10)] := by
  simp only [Network.intercept, Network.coefficients, Network.variance, Network.reverseAt, network,
    rows, reverseRows, List.drop, List.take, reverseFirst, reverseSecond,
    pairSlope, pairGain, pairVariance, combine, entry, List.map, List.zipWith,
    List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append, List.cons.injEq,
    and_true]
  and_intros <;> real_grind

public theorem reverseAt_one_moments :
    (network.reverseAt 1).mean = [one, selection.ofRat 3, zero] ∧
      swapAt 1 network.mean = [one, selection.ofRat 3, zero] ∧
      (network.reverseAt 1).covariance =
        [[selection.ofRat 2, selection.ofRat 4, zero],
          [selection.ofRat 4, selection.ofRat 18, selection.ofRat 3],
          [zero, selection.ofRat 3, one]] ∧
      swapMatrixAt 1 network.covariance =
        [[selection.ofRat 2, selection.ofRat 4, zero],
          [selection.ofRat 4, selection.ofRat 18, selection.ofRat 3],
          [zero, selection.ofRat 3, one]] := by
  refine ⟨?_, by rw [mean_closed]; rfl, ?_, by rw [covariance_closed]; rfl⟩
  · simp only [Network.mean, Network.reverseAt, network, rows, reverseRows, List.drop, List.take,
      reverseFirst, reverseSecond, pairSlope, pairGain, pairVariance, combine,
      entry, List.map, List.zipWith, List.getD_cons_zero, List.getD_cons_succ, List.foldl,
      meanAppend, dot, List.nil_append, List.cons_append, List.cons.injEq, and_true]
    and_intros <;> real_grind
  · simp only [Network.covariance, Network.reverseAt, network, rows, reverseRows, List.drop,
      List.take, reverseFirst, reverseSecond, pairSlope, pairGain, pairVariance,
      combine, entry, List.map, List.zipWith, List.getD_cons_zero, List.getD_cons_succ,
      List.foldl, covarianceAppend, dot, List.nil_append, List.cons_append, List.cons.injEq,
      and_true]
    and_intros <;> real_grind

/-! ### Both sides of the reversal, as certified integrals -/

private theorem swapIndex_below {index position : Nat} (adjacent : index < 2)
    (below : position < 3) :
    swapIndex index position < 3 := by
  unfold swapIndex
  split
  · omega
  · split <;> omega

private theorem reverseAt_mean (index : Nat) (adjacent : index < 2) :
    (network.reverseAt index).mean = swapAt index network.mean := by
  match index, adjacent with
  | 0, _ => exact reverseAt_zero_moments.1.trans reverseAt_zero_moments.2.1.symm
  | 1, _ => exact reverseAt_one_moments.1.trans reverseAt_one_moments.2.1.symm

/-- After reversing at either adjacent pair, both sides have the closed-form
means. The law pushed along the swap gets them from the network's own moments
(`pushed_moments`). The reversed network's law gets them from its own
recurrences (`moments_eq`). `moments_eq` carries the covariance closed forms
above to the second moments in the same way. -/
public theorem sides_mean (index : Nat) (adjacent : index < 2) {position : Nat}
    (below : position < 3) :
    HasRealIntegral (network.law.map (swapAt index) (swapAt_measurable index))
        (fun values => entry values position)
        (entry (swapAt index [one, zero, selection.ofRat 3]) position) ∧
      HasRealIntegral (network.reverseAt index).law (fun values => entry values position)
        (entry (swapAt index [one, zero, selection.ofRat 3]) position) := by
  have long : index + 1 < network.mean.length := by
    rw [mean_closed]
    simp only [List.length_cons, List.length_nil]
    omega
  constructor
  · have pushed := (network.pushed_moments (first := position) (second := position)
      (show index + 1 < 3 by omega) (swapIndex_below adjacent below)
      (swapIndex_below adjacent below)).1
    rw [← mean_closed, entry_swapAt long]
    exact pushed
  · have reversed := ((network.reverseAt index).moments_eq
      (show position < (network.reverseAt index).length by
        rw [Network.length_reverseAt]; exact below)
      (show position < (network.reverseAt index).length by
        rw [Network.length_reverseAt]; exact below)).1
    rw [← mean_closed, ← reverseAt_mean index adjacent]
    exact reversed

end
end Problib.Analysis.Gaussian.NetworkExample
