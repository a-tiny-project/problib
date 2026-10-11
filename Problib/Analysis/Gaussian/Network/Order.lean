module

public import Problib.Analysis.Gaussian.Network.Moments
import Problib.Real.Grind

/-! Order independence: the network of a permuted mean and covariance.

`ofMoments m Σ` regresses each node on the nodes before it, so it depends on the
order of the coordinates. Its law does not. Reversing adjacent nodes moves the
law along the swap (`reverse`), and the reversed network's mean and covariance
recurrences are the old ones with the two positions exchanged
(`reverseAt_mean`, `reverseAt_covariance`). These come from the moments of the
two laws (`moments_eq`, `pushed_moments`), which are equal because the laws
are. Along a word of adjacent swaps the reversed network `N′` therefore has the
permuted mean and covariance. Fixed-order uniqueness (`ofMoments_self`)
identifies `N′` with `ofMoments` of the permuted moments (`ofMoments_permute`).

`N′` also shows that the permuted covariance has positive pivots
(`positivePivots_permute`), so the permuted side needs no second premise. A
permutation is given as a word of adjacent swaps (`permute`). Every permutation
of a finite list is such a word, so quantifying over words covers every order.
No multidimensional Jacobian appears, and nothing claims that moments determine
distributions in general: uniqueness is stated for networks only.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Reading a swapped list -/

public theorem swapIndex_below {index position count : Nat} (long : index + 1 < count)
    (below : position < count) : swapIndex index position < count := by
  unfold swapIndex
  split
  · omega
  · split <;> omega

public theorem getElem?_swapAt {α : Type} :
    ∀ (index : Nat) (values : List α) (position : Nat), index + 1 < values.length →
      (swapAt index values)[position]? = values[swapIndex index position]?
  | 0, _ :: _ :: _, 0, _ => rfl
  | 0, _ :: _ :: _, 1, _ => rfl
  | 0, _ :: _ :: _, position + 2, _ => by
      simp [swapAt, swapIndex]
  | index + 1, _ :: _, 0, _ => by
      simp [swapAt, swapIndex]
  | index + 1, _ :: rest, position + 1, long => by
      simp only [swapAt, List.getElem?_cons_succ]
      rw [getElem?_swapAt index rest position (by simpa using long)]
      have shifted : swapIndex (index + 1) (position + 1) = swapIndex index position + 1 := by
        unfold swapIndex
        by_cases left : position = index
        · simp [left]
        · by_cases right : position = index + 1
          · simp [right]
          · simp [left, right]
      rw [shifted, List.getElem?_cons_succ]

public theorem getD_swapAt {α : Type} {index : Nat} {values : List α} (fallback : α)
    (long : index + 1 < values.length) (position : Nat) :
    (swapAt index values).getD position fallback =
      values.getD (swapIndex index position) fallback := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_swapAt index values position long]

/-- Two lists of rows of equal shape and equal entries are equal. -/
public theorem ext_rows {left right : List (List Carrier)} (length : left.length = right.length)
    (rows : ∀ first, first < left.length → (left.getD first []).length = (right.getD first []).length)
    (entries : ∀ first second, first < left.length → second < (left.getD first []).length →
      entry (left.getD first []) second = entry (right.getD first []) second) :
    left = right := by
  apply List.ext_getElem length
  intro first leftBelow rightBelow
  have leftRow : left.getD first [] = left[first] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem leftBelow]
    rfl
  have rightRow : right.getD first [] = right[first] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rightBelow]
    rfl
  rw [← leftRow, ← rightRow]
  exact ext_entry (rows first leftBelow) (entries first · leftBelow)

/-! ### The moments of one reversal -/

public theorem Network.reverseAt_short {network : Network} {index : Nat}
    (short : network.length ≤ index + 1) : network.reverseAt index = network :=
  Network.ext (reverseRows_short short)

/-- The reversed network's mean recurrence, read at the swapped position. -/
public theorem Network.reverseAt_meanAt (network : Network) {index position : Nat}
    (long : index + 1 < network.length) (below : position < network.length) :
    (network.reverseAt index).meanAt position = network.meanAt (swapIndex index position) := by
  have swapped := swapIndex_below long below
  have reversed := ((network.reverseAt index).moments_eq (first := position) (second := position)
    (by rw [Network.length_reverseAt]; exact below)
    (by rw [Network.length_reverseAt]; exact below)).1
  rw [← network.reverse index] at reversed
  exact reversed.unique (network.pushed_moments long swapped swapped).1

/-- The reversed network's covariance recurrence, read at the swapped positions. -/
public theorem Network.reverseAt_covarianceAt (network : Network) {index first second : Nat}
    (long : index + 1 < network.length) (firstBelow : first < network.length)
    (secondBelow : second < network.length) :
    (network.reverseAt index).covarianceAt first second =
      network.covarianceAt (swapIndex index first) (swapIndex index second) := by
  have reversed := ((network.reverseAt index).moments_eq (first := first) (second := second)
    (by rw [Network.length_reverseAt]; exact firstBelow)
    (by rw [Network.length_reverseAt]; exact secondBelow)).2
  rw [← network.reverse index] at reversed
  have value := reversed.unique (network.pushed_moments long (swapIndex_below long firstBelow)
    (swapIndex_below long secondBelow)).2
  rw [network.reverseAt_meanAt long firstBelow, network.reverseAt_meanAt long secondBelow] at value
  real_grind

/-- Reversing nodes `i` and `i + 1` swaps positions `i` and `i + 1` of the mean. -/
public theorem Network.reverseAt_mean (network : Network) (index : Nat) :
    (network.reverseAt index).mean = swapAt index network.mean := by
  by_cases long : index + 1 < network.length
  · have meanLength := network.shape.1
    apply ext_entry (by rw [swapAt_length, (network.reverseAt index).shape.1,
      Network.length_reverseAt, meanLength])
    intro position below
    rw [(network.reverseAt index).shape.1, Network.length_reverseAt] at below
    rw [← Network.meanAt, network.reverseAt_meanAt long below,
      entry_swapAt (by rw [meanLength]; exact long)]
    rfl
  · rw [Network.reverseAt_short (by omega), swapAt_of_le (by rw [network.shape.1]; omega)]

/-- Reversing nodes `i` and `i + 1` swaps rows and columns `i` and `i + 1` of
the covariance. -/
public theorem Network.reverseAt_covariance (network : Network) (index : Nat) :
    (network.reverseAt index).covariance = swapMatrixAt index network.covariance := by
  obtain ⟨_, covarianceLength, rowLength⟩ := network.shape
  by_cases long : index + 1 < network.length
  · obtain ⟨_, reversedLength, reversedRow⟩ := (network.reverseAt index).shape
    rw [Network.length_reverseAt] at reversedLength reversedRow
    have readRow : ∀ position, position < network.length →
        (network.covariance.getD position []).length = network.length := fun position below =>
      rowLength _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _)
    have readReversed : ∀ position, position < network.length →
        ((network.reverseAt index).covariance.getD position []).length = network.length :=
      fun position below => reversedRow _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _)
    have readSwapped : ∀ position, (swapMatrixAt index network.covariance).getD position [] =
        swapAt index (network.covariance.getD (swapIndex index position) []) := by
      intro position
      unfold swapMatrixAt
      rw [getD_swapAt _ (by rw [List.length_map]; omega), List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getD_eq_getElem?_getD]
      cases network.covariance[swapIndex index position]? with
      | none => cases index <;> rfl
      | some _ => rfl
    apply ext_rows (by rw [reversedLength, swapMatrixAt, swapAt_length, List.length_map,
      covarianceLength])
    · intro position below
      rw [reversedLength] at below
      rw [readReversed position below, readSwapped, swapAt_length,
        readRow _ (swapIndex_below long below)]
    · intro first second firstBelow secondBelow
      rw [reversedLength] at firstBelow
      rw [readReversed first firstBelow] at secondBelow
      have value := network.reverseAt_covarianceAt long firstBelow secondBelow
      unfold Network.covarianceAt at value
      have rowLong : index + 1 <
          (network.covariance.getD (swapIndex index first) []).length := by
        rw [readRow _ (swapIndex_below long firstBelow)]
        exact long
      rw [value, readSwapped, entry_swapAt rowLong]
  · rw [Network.reverseAt_short (by omega)]
    unfold swapMatrixAt
    have rows : network.covariance.map (swapAt index) = network.covariance := by
      conv => rhs; rw [← List.map_id network.covariance]
      apply List.map_congr_left
      intro row member
      exact swapAt_of_le (by rw [rowLength row member]; omega)
    rw [rows, swapAt_of_le (by rw [covarianceLength]; omega)]

/-! ### Along a word of swaps -/

/-- Apply a word of adjacent swaps to the rows and the columns of a matrix. -/
@[expose] public def permuteMatrix (word : List Nat) (matrix : List (List Carrier)) :
    List (List Carrier) :=
  word.foldl (fun current index => swapMatrixAt index current) matrix

public theorem Network.reverseAlong_mean (network : Network) (word : List Nat) :
    (network.reverseAlong word).mean = permute word network.mean := by
  induction word generalizing network with
  | nil => rfl
  | cons index word induction =>
      change ((network.reverseAt index).reverseAlong word).mean = _
      rw [induction, network.reverseAt_mean]
      rfl

public theorem Network.reverseAlong_covariance (network : Network) (word : List Nat) :
    (network.reverseAlong word).covariance = permuteMatrix word network.covariance := by
  induction word generalizing network with
  | nil => rfl
  | cons index word induction =>
      change ((network.reverseAt index).reverseAlong word).covariance = _
      rw [induction, network.reverseAt_covariance]
      rfl

/-! ### Order independence -/

variable {mean : List Carrier} {covariance : List (List Carrier)}

/-- A permuted covariance with positive pivots has positive pivots: the
network reversed along the word has it as its covariance. -/
public theorem positivePivots_permute (positive : PositivePivots covariance)
    (symmetric : Symmetric covariance) (square : Square covariance) (word : List Nat) :
    PositivePivots (permuteMatrix word covariance) := by
  have reversed := ((ofMoments [] covariance positive).reverseAlong word).positivePivots
  rwa [Network.reverseAlong_covariance, ofMoments_covariance positive symmetric square] at reversed

/-- Order independence: the law of `ofMoments m Σ` pushed along a word of
adjacent swaps is the law of `ofMoments` of the permuted mean and covariance.
Every permutation of a finite list is a word of adjacent swaps, so this covers
every order of the coordinates. -/
public theorem ofMoments_permute (positive : PositivePivots covariance)
    (symmetric : Symmetric covariance) (square : Square covariance)
    (meanLength : mean.length = covariance.length) (word : List Nat) :
    (ofMoments mean covariance positive).law.map (permute word) (permute_measurable word) =
      (ofMoments (permute word mean) (permuteMatrix word covariance)
        (positivePivots_permute positive symmetric square word)).law := by
  rw [Network.reverse_along]
  congr 1
  apply Network.ext
  change _ = regress (permute word mean) (permuteMatrix word covariance)
  rw [← Network.regress_self, Network.reverseAlong_mean, Network.reverseAlong_covariance,
    ofMoments_mean positive symmetric meanLength, ofMoments_covariance positive symmetric square]

end
end Problib.Analysis.Gaussian
