module

public import Problib.Analysis.Gaussian.Network.Law
import Problib.Real.Grind
import Problib.Measure.Measurability.Real

/-! Reversing an adjacent pair of nodes in a linear-Gaussian network.

Two adjacent nodes `x ~ N(a, p)` and `y ~ N(b + c x, q)`, with `a` and `b`
affine in the earlier nodes, have the same joint density as
`y ~ N(b + c a, s)` and `x ~ N(a + k (y - b - c a), p q / s)`, where
`s = q + c² p` and `k = p c / s` (`density_reverse_pair`). The identity is
pointwise in `a`, `b`, `x` and `y`, and holds at every `c`, zero included.

`Network.reverseAt i` rebuilds rows `i` and `i + 1` from it and swaps
columns `i` and `i + 1` in every later row. Both rebuilt rows regress on the
union of the two old parent sets, which is the fill-in. Its density at the
swapped list is the old density (`density_reverseAt`), list volume is
invariant under the swap (`listVolume_swapAt`), so the law pushed along the
swap is the law of the reversed network (`reverse`). A word of adjacent swaps
reverses along each in turn (`reverse_along`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### The pair identity -/

/-- The marginal variance `s = q + c² p` of the second node. -/
@[expose] public def pairVariance (first second slope : Carrier) : Carrier :=
  add second (mul (mul slope slope) first)

/-- The gain `k = p c / s` of the first node on the second. -/
@[expose] public def pairGain (first second slope : Carrier) : Carrier :=
  div (mul first slope) (pairVariance first second slope)

public theorem pairVariance_positive {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) (slope : Carrier) :
    lt zero (pairVariance first second slope) := by
  have square : le zero (mul (mul slope slope) first) :=
    mul_nonnegative (mul_self_nonnegative slope) firstPositive.1
  unfold pairVariance
  real_grind

/-- The conditional variance `p q / s` of the first node given the second. -/
public theorem pairConditional_positive {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) (slope : Carrier) :
    lt zero (div (mul first second) (pairVariance first second slope)) :=
  div_positive (mul_positive firstPositive secondPositive)
    (pairVariance_positive firstPositive secondPositive slope)

private theorem pair_exponent {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) (front back slope value next : Carrier) :
    add (neg (div (mul (sub value front) (sub value front)) (mul (selection.ofRat 2) first)))
        (neg (div (mul (sub next (add back (mul slope value))) (sub next (add back
          (mul slope value))))
          (mul (selection.ofRat 2) second))) =
      add (neg (div (mul (sub next (add back (mul slope front))) (sub next (add back
        (mul slope front))))
          (mul (selection.ofRat 2) (pairVariance first second slope))))
        (neg (div (mul (sub value (add front (mul (pairGain first second slope)
            (sub next (add back (mul slope front))))))
            (sub value (add front (mul (pairGain first second slope)
              (sub next (add back (mul slope front)))))))
          (mul (selection.ofRat 2) (div (mul first second)
            (pairVariance first second slope))))) := by
  have firstNonzero := (positive_iff_nonnegative_and_nonzero.mp firstPositive).2
  have secondNonzero := (positive_iff_nonnegative_and_nonzero.mp secondPositive).2
  have sumPositive := pairVariance_positive firstPositive secondPositive slope
  have conditionalPositive := pairConditional_positive firstPositive secondPositive slope
  have nonzero : ∀ {value : Carrier}, lt zero value → value ≠ zero :=
    fun positive => (positive_iff_nonnegative_and_nonzero.mp positive).2
  have sumNonzero := nonzero sumPositive
  have productNonzero := nonzero (mul_positive firstPositive secondPositive)
  have conditionalNonzero := nonzero conditionalPositive
  have firstScaled := nonzero (mul_positive ofRat_two_positive firstPositive)
  have secondScaled := nonzero (mul_positive ofRat_two_positive secondPositive)
  have sumScaled := nonzero (mul_positive ofRat_two_positive sumPositive)
  have conditionalScaled := nonzero (mul_positive ofRat_two_positive conditionalPositive)
  unfold pairGain pairVariance at *
  real_grind

private theorem pair_normalizer {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) (slope : Carrier) :
    NNReal.mul (normalizer first) (normalizer second) =
      NNReal.mul (normalizer (pairVariance first second slope))
        (normalizer (div (mul first second) (pairVariance first second slope))) := by
  have sumPositive := pairVariance_positive firstPositive secondPositive slope
  have conditionalPositive := pairConditional_positive firstPositive secondPositive slope
  have sumNonzero := (positive_iff_nonnegative_and_nonzero.mp sumPositive).2
  have scale : le zero (mul (selection.ofRat 2) pi) :=
    (mul_positive ofRat_two_positive pi_positive).1
  have product : mul (mul (mul (selection.ofRat 2) pi) first)
      (mul (mul (selection.ofRat 2) pi) second) =
      mul (mul (mul (selection.ofRat 2) pi) (pairVariance first second slope))
        (mul (mul (selection.ofRat 2) pi)
          (div (mul first second) (pairVariance first second slope))) := by
    real_grind
  unfold normalizer
  rw [← sqrt_mul, ← sqrt_mul,
    ← NNReal.ofReal_mul (mul_nonnegative scale firstPositive.1)
      (mul_nonnegative scale secondPositive.1),
    ← NNReal.ofReal_mul (mul_nonnegative scale sumPositive.1)
      (mul_nonnegative scale conditionalPositive.1), product]

/-- Reversing two adjacent Gaussian nodes, pointwise. The first node `x` has
mean `a` and variance `p`. The second node `y` has mean `b + c x` and variance
`q`. Reversed, `y` has mean `b + c a` and variance `s = q + c² p`, and `x` given
`y` has mean `a + k (y - b - c a)` and variance `p q / s`, with `k = p c / s`.
Both variances must be positive. The slope `c` is arbitrary, zero included. -/
public theorem density_reverse_pair {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) (front back slope value next : Carrier) :
    NNReal.mul (density front first value) (density (add back (mul slope value)) second next) =
      NNReal.mul (density (add back (mul slope front)) (pairVariance first second slope) next)
        (density (add front (mul (pairGain first second slope) (sub next (add back
          (mul slope front)))))
          (div (mul first second) (pairVariance first second slope)) value) := by
  have nonzero : ∀ variance, lt zero variance → (normalizer variance).toReal ≠ zero :=
    fun variance positive => (positive_iff_nonnegative_and_nonzero.mp
      (normalizer_positive variance positive)).2
  have firstNonzero := nonzero first firstPositive
  have secondNonzero := nonzero second secondPositive
  have sumNonzero := nonzero _ (pairVariance_positive firstPositive secondPositive slope)
  have conditionalNonzero := nonzero _ (pairConditional_positive firstPositive secondPositive slope)
  have exponents := congrArg exp (pair_exponent firstPositive secondPositive front back slope value
    next)
  rw [exp_add, exp_add] at exponents
  have normalizers := congrArg NNReal.toReal (pair_normalizer firstPositive secondPositive slope)
  rw [NNReal.toReal_mul, NNReal.toReal_mul] at normalizers
  have leftNonzero : mul (normalizer first).toReal (normalizer second).toReal ≠ zero :=
    fun vanished => (mul_eq_zero_iff.mp vanished).elim firstNonzero secondNonzero
  have rightNonzero : mul (normalizer (pairVariance first second slope)).toReal
      (normalizer (div (mul first second) (pairVariance first second slope))).toReal ≠ zero :=
    fun vanished => (mul_eq_zero_iff.mp vanished).elim sumNonzero conditionalNonzero
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_mul, density_toReal, density_toReal, density_toReal,
    density_toReal]
  real_grind

/-! ### The swap of adjacent positions -/

public theorem swapAt_measurable (index : Nat) :
    MeasurableMap (Space.list borel) (Space.list borel) (swapAt (α := Carrier) index) := by
  induction index with
  | zero =>
      have equal : swapAt (α := Carrier) 0 = fun values =>
          if 2 ≤ values.length then entry values 1 :: entry values 0 :: values.tail.tail
          else values := by
        funext values
        match values with
        | [] => rfl
        | [_] => rfl
        | first :: second :: rest => simp [swapAt, entry]
      rw [equal]
      apply MeasurableMap.ite
      · exact ListSpace.length_measurable borel (set := fun length => 2 ≤ length) trivial
      · measurability [entry_measurable 0, entry_measurable 1, ListSpace.tail_measurable borel,
          ListSpace.cons_measurable borel]
      · exact MeasurableMap.identity _
  | succ index induction =>
      have equal : swapAt (α := Carrier) (index + 1) = fun values =>
          if values.length = 0 then values else entry values 0 :: swapAt index values.tail := by
        funext values
        match values with
        | [] => rfl
        | first :: rest => simp [swapAt, entry]
      rw [equal]
      apply MeasurableMap.ite
      · exact ListSpace.length_measurable borel (set := fun length => length = 0) trivial
      · exact MeasurableMap.identity _
      · measurability [entry_measurable 0, induction, ListSpace.tail_measurable borel,
          ListSpace.cons_measurable borel]

/-- Inserting one place later and swapping is inserting in place. -/
public theorem swapAt_insertIdx {α : Type} (index : Nat) (values : List α) (value : α)
    (long : index + 1 ≤ values.length) :
    swapAt index (values.insertIdx (index + 1) value) = values.insertIdx index value := by
  induction index generalizing values with
  | zero =>
      match values, long with
      | first :: rest, _ => simp [swapAt]
  | succ index induction =>
      match values, long with
      | first :: rest, long =>
          simp only [List.insertIdx_succ_cons, swapAt]
          rw [induction rest (by simpa using long)]

/-- List volume is invariant under the swap of two adjacent positions. -/
public theorem listVolume_swapAt (count index : Nat) :
    (listVolume count).map (swapAt index) (swapAt_measurable index) = listVolume count := by
  have complement : ∀ length, Set.complement (fun pair : List Carrier × Carrier =>
      pair.1.length = length) =
      Set.product (fun values : List Carrier => values.length ≠ length) Set.univ := by
    intro length
    funext pair
    exact propext ⟨fun different => ⟨different, True.intro⟩, fun inside => inside.1⟩
  have lengthMeasurable : ∀ length, (Space.list borel).Measurable
      (fun values : List Carrier => values.length ≠ length) := fun length =>
    ListSpace.length_measurable borel (set := fun current => current ≠ length) trivial
  by_cases inside : index + 1 < count
  · obtain ⟨shorter, rfl⟩ : ∃ shorter, count = shorter + 1 := ⟨count - 1, by omega⟩
    have later : index + 1 ≤ shorter := by omega
    unfold listVolume
    calc (Measure.listPower volume volumeSFinite (shorter + 1)).map (swapAt index) _
        = ((Measure.prod (Measure.listPower volume volumeSFinite shorter) volume
            volumeSFinite).map (fun input => input.1.insertIdx (index + 1) input.2)
            (insert_at_measurable borel (index + 1))).map (swapAt index)
            (swapAt_measurable index) := by
          rw [Measure.insertIdx_power volume volumeSFinite later]
      _ = (Measure.prod (Measure.listPower volume volumeSFinite shorter) volume
            volumeSFinite).map (fun input => input.1.insertIdx index input.2)
            (insert_at_measurable borel index) := by
          rw [Measure.map_comp]
          apply Measure.map_congr_on _ (region := fun pair : List Carrier × Carrier =>
            pair.1.length = shorter)
          · rw [complement, Measure.prod_apply_product _ _ _ (lengthMeasurable shorter) borel.univ,
              Measure.listPower_length_null, ENNReal.zero_mul]
          · intro pair counted
            exact swapAt_insertIdx index pair.1 pair.2 (by rw [counted]; exact later)
      _ = Measure.listPower volume volumeSFinite (shorter + 1) :=
          Measure.insertIdx_power volume volumeSFinite (by omega)
  · calc (listVolume count).map (swapAt index) (swapAt_measurable index)
        = (listVolume count).map (fun values => values) (MeasurableMap.identity _) := by
          apply Measure.map_congr_on _ (region := fun values : List Carrier =>
            values.length = count)
          · exact listVolume_length_null count
          · intro values counted
            exact swapAt_of_le (by omega)
      _ = listVolume count := Measure.map_id _

/-! ### Readings of a swapped list -/

public theorem entry_swapAt_below {index position : Nat} (below : position < index)
    (values : List Carrier) : entry (swapAt index values) position = entry values position := by
  induction index generalizing position values with
  | zero => cases below
  | succ index induction =>
      match values, position with
      | [], _ => rfl
      | _ :: _, 0 => rfl
      | _ :: rest, position + 1 =>
          simp only [swapAt, entry, List.getD_cons_succ]
          exact induction (by omega) rest

public theorem entry_swapAt_above {index position : Nat} (above : index + 1 < position)
    (values : List Carrier) : entry (swapAt index values) position = entry values position := by
  induction index generalizing position values with
  | zero =>
      match values, position with
      | [], _ => rfl
      | [_], _ => rfl
      | _ :: _ :: _, position + 2 => rfl
  | succ index induction =>
      match values, position with
      | [], _ => rfl
      | _ :: rest, position + 1 =>
          simp only [swapAt, entry, List.getD_cons_succ]
          exact induction (by omega) rest

public theorem entry_swapAt_left {index : Nat} {values : List Carrier}
    (long : index + 1 < values.length) :
    entry (swapAt index values) index = entry values (index + 1) := by
  induction index generalizing values with
  | zero =>
      match values, long with
      | _ :: _ :: _, _ => rfl
  | succ index induction =>
      match values, long with
      | _ :: rest, long =>
          simp only [swapAt, entry, List.getD_cons_succ]
          exact induction (by simpa using long)

public theorem entry_swapAt_right {index : Nat} {values : List Carrier}
    (long : index + 1 < values.length) :
    entry (swapAt index values) (index + 1) = entry values index := by
  induction index generalizing values with
  | zero =>
      match values, long with
      | _ :: _ :: _, _ => rfl
  | succ index induction =>
      match values, long with
      | _ :: rest, long =>
          simp only [swapAt, entry, List.getD_cons_succ]
          exact induction (by simpa using long)

/-- Coefficients on the nodes before the swap do not see it. -/
public theorem dot_swapAt_below {index : Nat} {coefficients : List Carrier}
    (short : coefficients.length ≤ index) (values : List Carrier) :
    dot coefficients (swapAt index values) = dot coefficients values := by
  rw [dot_eq_sumBelow, dot_eq_sumBelow]
  exact sumBelow_congr fun position below => by
    rw [entry_swapAt_below (by omega)]

/-- Swapping both the coefficients and the values leaves the sum unchanged. -/
public theorem dot_swapAt_swapAt {index : Nat} {coefficients values : List Carrier}
    (longCoefficients : index + 1 < coefficients.length) (longValues : index + 1 < values.length) :
    dot (swapAt index coefficients) (swapAt index values) = dot coefficients values := by
  induction index generalizing coefficients values with
  | zero =>
      match coefficients, values, longCoefficients, longValues with
      | first :: second :: rest, value :: next :: others, _, _ =>
          change add (mul second next) (add (mul first value) (dot rest others)) =
            add (mul first value) (add (mul second next) (dot rest others))
          real_grind
  | succ index induction =>
      match coefficients, values, longCoefficients, longValues with
      | first :: rest, value :: others, longCoefficients, longValues =>
          change add (mul first value) (dot (swapAt index rest) (swapAt index others)) =
            add (mul first value) (dot rest others)
          rw [induction (by simpa using longCoefficients) (by simpa using longValues)]

public theorem entry_take {count position : Nat} (below : position < count)
    (values : List Carrier) :
    entry (values.take count) position = entry values position := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt below]

/-- Split the last coefficient off a row of `i + 1` coefficients. -/
public theorem dot_split_last {index : Nat} {coefficients : List Carrier}
    (counted : coefficients.length = index + 1) (values : List Carrier) :
    dot coefficients values =
      add (dot (coefficients.take index) values)
        (mul (entry coefficients index) (entry values index)) := by
  rw [dot_eq_sumBelow, dot_eq_sumBelow, counted, List.length_take, counted,
    Nat.min_eq_left (Nat.le_succ index)]
  change add (sumBelow index _) _ = _
  congr 1
  exact sumBelow_congr fun position below => by rw [entry_take below]

public theorem dot_concat {index : Nat} {coefficients : List Carrier}
    (counted : coefficients.length = index) (last : Carrier) (values : List Carrier) :
    dot (coefficients ++ [last]) values =
      add (dot coefficients values) (mul last (entry values index)) := by
  rw [dot_split_last (index := index) (by simp [counted]), List.take_left' counted, ← counted,
    entry_concat_length]

/-- `left + s · right`, entrywise over the shorter list. -/
@[expose] public def combine (scalar : Carrier) (left right : List Carrier) : List Carrier :=
  List.zipWith (fun first second => add first (mul scalar second)) left right

@[simp] public theorem combine_length (scalar : Carrier) (left right : List Carrier) :
    (combine scalar left right).length = min left.length right.length :=
  List.length_zipWith

public theorem dot_combine (scalar : Carrier) {left right : List Carrier}
    (same : left.length = right.length) (values : List Carrier) :
    dot (combine scalar left right) values =
      add (dot left values) (mul scalar (dot right values)) := by
  induction left generalizing right values with
  | nil =>
      cases right with
      | nil =>
          change zero = add (dot [] values) (mul scalar (dot [] values))
          rw [dot_nil_left]
          real_grind
      | cons _ _ => cases same
  | cons first rest induction =>
      cases right with
      | nil => cases same
      | cons second others =>
          change dot (add first (mul scalar second) :: combine scalar rest others) values = _
          rw [dot_cons_left, dot_cons_left, dot_cons_left,
            induction (by simpa using same)]
          real_grind

/-! ### The reversed rows -/

/-- Row `i + 1`'s coefficient on node `i`. -/
@[expose] public def pairSlope (index : Nat) (second : Row) : Carrier :=
  entry second.coefficients index

/-- Row `i` after the reversal: the old node `i + 1` regressed on the nodes
before `i`. Its coefficients are the union of both old parent sets, which is
the fill-in. -/
@[expose] public def reverseFirst (index : Nat) (first second : Row) : Row where
  intercept := add second.intercept (mul (pairSlope index second) first.intercept)
  coefficients := combine (pairSlope index second) (second.coefficients.take index)
    first.coefficients
  variance := pairVariance first.variance second.variance (pairSlope index second)

/-- Row `i + 1` after the reversal: the old node `i` regressed on the nodes
before `i` and on the old node `i + 1`, now at position `i`. -/
@[expose] public def reverseSecond (index : Nat) (first second : Row) : Row where
  intercept := sub first.intercept
    (mul (pairGain first.variance second.variance (pairSlope index second))
      (reverseFirst index first second).intercept)
  coefficients := combine (neg (pairGain first.variance second.variance (pairSlope index second)))
      first.coefficients (reverseFirst index first second).coefficients ++
    [pairGain first.variance second.variance (pairSlope index second)]
  variance := div (mul first.variance second.variance)
    (pairVariance first.variance second.variance (pairSlope index second))

/-- A later row reads the two swapped nodes in swapped columns. -/
@[expose] public def Row.swapColumns (index : Nat) (row : Row) : Row where
  intercept := row.intercept
  coefficients := swapAt index row.coefficients
  variance := row.variance

/-- The rows after reversing positions `i` and `i + 1`, unchanged when the
network has no node `i + 1`. -/
@[expose] public def reverseRows (index : Nat) (rows : List Row) : List Row :=
  match rows.drop index with
  | first :: second :: back =>
      rows.take index ++ reverseFirst index first second :: reverseSecond index first second ::
        back.map (Row.swapColumns index)
  | _ => rows

public theorem reverseRows_split {index : Nat} {front : List Row} (first second : Row)
    (back : List Row) (counted : front.length = index) :
    reverseRows index (front ++ first :: second :: back) =
      front ++ reverseFirst index first second :: reverseSecond index first second ::
        back.map (Row.swapColumns index) := by
  unfold reverseRows
  rw [List.drop_left' counted, List.take_left' counted]

public theorem reverseRows_short {index : Nat} {rows : List Row}
    (short : rows.length ≤ index + 1) : reverseRows index rows = rows := by
  unfold reverseRows
  split
  · rename_i first second back dropped
    have counted := congrArg List.length dropped
    simp only [List.length_drop, List.length_cons] at counted
    omega
  · rfl

/-- A list with positions `i` and `i + 1` splits around them. -/
public theorem rows_split {index : Nat} {rows : List Row} (long : index + 1 < rows.length) :
    ∃ front first second back, rows = front ++ first :: second :: back ∧ front.length = index := by
  refine ⟨rows.take index, ?_⟩
  have counted : (rows.take index).length = index := by
    rw [List.length_take]
    omega
  match dropped : rows.drop index with
  | first :: second :: back =>
      exact ⟨first, second, back, by rw [← dropped, List.take_append_drop], counted⟩
  | [] =>
      have := congrArg List.length dropped
      simp only [List.length_drop, List.length_nil] at this
      omega
  | [_] =>
      have := congrArg List.length dropped
      simp only [List.length_drop, List.length_cons, List.length_nil] at this
      omega

/-- The rows of a triangular list around positions `i` and `i + 1`. -/
private theorem split_shape {index : Nat} {front back : List Row} {first second : Row}
    (triangular : Triangular (front ++ first :: second :: back)) (counted : front.length = index) :
    first.coefficients.length = index ∧ second.coefficients.length = index + 1 ∧
      ∀ position row, back[position]? = some row →
        row.coefficients.length = index + 2 + position := by
  refine ⟨triangular index first ?_, triangular (index + 1) second ?_, fun position row found =>
    triangular (index + 2 + position) row ?_⟩
  · rw [List.getElem?_append_right (by omega), counted, Nat.sub_self]
    rfl
  · rw [List.getElem?_append_right (by omega), counted, Nat.add_sub_cancel_left]
    rfl
  · rw [List.getElem?_append_right (by omega), counted,
      show index + 2 + position - index = position + 2 by omega]
    exact found

public theorem reverseRows_triangular {index : Nat} {rows : List Row}
    (triangular : Triangular rows) : Triangular (reverseRows index rows) := by
  by_cases long : index + 1 < rows.length
  · obtain ⟨front, first, second, back, rfl, counted⟩ := rows_split long
    obtain ⟨firstShape, secondShape, backShape⟩ := split_shape triangular counted
    rw [reverseRows_split first second back counted]
    intro position row found
    by_cases inFront : position < front.length
    · rw [List.getElem?_append_left inFront] at found
      exact triangular position row (by rw [List.getElem?_append_left inFront]; exact found)
    · rw [List.getElem?_append_right (by omega)] at found
      obtain ⟨offset, rfl⟩ : ∃ offset, position = front.length + offset :=
        ⟨position - front.length, by omega⟩
      rw [Nat.add_sub_cancel_left] at found
      match offset, found with
      | 0, found =>
          cases Option.some.inj found
          simp [reverseFirst, List.length_take, firstShape, secondShape, counted]
      | 1, found =>
          cases Option.some.inj found
          simp [reverseSecond, reverseFirst, List.length_take, firstShape, secondShape, counted]
      | offset + 2, found =>
          simp only [List.getElem?_cons_succ, List.getElem?_map] at found
          match backed : back[offset]?, found with
          | some original, found =>
              cases Option.some.inj found
              simp only [Row.swapColumns, swapAt_length, backShape offset original backed, counted]
              omega
  · rw [reverseRows_short (by omega)]
    exact triangular

public theorem reverseRows_positive {index : Nat} {rows : List Row}
    (positive : ∀ row ∈ rows, lt zero row.variance) :
    ∀ row ∈ reverseRows index rows, lt zero row.variance := by
  by_cases long : index + 1 < rows.length
  · obtain ⟨front, first, second, back, rfl, counted⟩ := rows_split long
    rw [reverseRows_split first second back counted]
    have firstPositive := positive first (by simp)
    have secondPositive := positive second (by simp)
    intro row member
    simp only [List.mem_append, List.mem_cons, List.mem_map] at member
    rcases member with inFront | rfl | rfl | ⟨original, inBack, rfl⟩
    · exact positive row (by simp [inFront])
    · exact pairVariance_positive firstPositive secondPositive _
    · exact pairConditional_positive firstPositive secondPositive _
    · exact positive original (by simp [inBack])
  · rw [reverseRows_short (by omega)]
    exact positive

/-- Reverse nodes `i` and `i + 1`. The network is unchanged when it has no
node `i + 1`. -/
@[expose] public def Network.reverseAt (network : Network) (index : Nat) : Network where
  rows := reverseRows index network.rows
  triangular := reverseRows_triangular network.triangular
  positive := reverseRows_positive network.positive

@[simp] public theorem Network.length_reverseAt (network : Network) (index : Nat) :
    (network.reverseAt index).length = network.length := by
  unfold Network.length
  change (reverseRows index network.rows).length = network.rows.length
  by_cases long : index + 1 < network.rows.length
  · obtain ⟨front, first, second, back, split, counted⟩ := rows_split long
    simp only [split, reverseRows_split first second back counted, List.length_append,
      List.length_cons, List.length_map]
  · rw [reverseRows_short (by omega)]

/-! ### The density of the reversed network -/

public theorem conditionals_append_rows (front back : List Row) (start : Nat)
    (values : List Carrier) :
    conditionals (front ++ back) start values =
      NNReal.mul (conditionals front start values)
        (conditionals back (start + front.length) values) := by
  induction front generalizing start with
  | nil => simp [conditionals, NNReal.one_mul]
  | cons row front induction =>
      simp only [List.cons_append, conditionals, induction, NNReal.mul_assoc, List.length_cons]
      rw [show start + 1 + front.length = start + (front.length + 1) by omega]

/-- Rows before the swap read neither swapped node. -/
private theorem conditionals_swap_front {index : Nat} (rows : List Row) (start : Nat)
    (reads : ∀ position row, rows[position]? = some row →
      row.coefficients.length ≤ index ∧ start + position < index) (values : List Carrier) :
    conditionals rows start (swapAt index values) = conditionals rows start values := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows induction =>
      obtain ⟨short, below⟩ := reads 0 row rfl
      have rest := induction (start + 1) (fun position current found => by
        have read := reads (position + 1) current found
        exact ⟨read.1, by omega⟩)
      simp only [conditionals, rest, Row.density, Row.mean, dot_swapAt_below short,
        entry_swapAt_below (show start < index by omega)]

/-- Rows after the swap read both swapped nodes in swapped columns. -/
private theorem conditionals_swap_back {index : Nat} (rows : List Row) (start : Nat)
    (reads : ∀ position row, rows[position]? = some row →
      index + 1 < row.coefficients.length ∧ index + 1 < start + position)
    {values : List Carrier} (long : index + 1 < values.length) :
    conditionals (rows.map (Row.swapColumns index)) start (swapAt index values) =
      conditionals rows start values := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows induction =>
      obtain ⟨wide, above⟩ := reads 0 row rfl
      have rest := induction (start + 1) (fun position current found => by
        have read := reads (position + 1) current found
        exact ⟨read.1, by omega⟩)
      simp only [List.map_cons, conditionals, rest]
      congr 1
      show density (add row.intercept (dot (swapAt index row.coefficients) (swapAt index values)))
          row.variance (entry (swapAt index values) start) =
        density (add row.intercept (dot row.coefficients values)) row.variance (entry values start)
      rw [dot_swapAt_swapAt wide long, entry_swapAt_above (show index + 1 < start by omega)]

private theorem second_mean {index : Nat} {second : Row}
    (counted : second.coefficients.length = index + 1) (values : List Carrier) :
    second.mean values =
      add (add second.intercept (dot (second.coefficients.take index) values))
        (mul (pairSlope index second) (entry values index)) := by
  unfold Row.mean pairSlope
  rw [dot_split_last counted]
  real_grind

private theorem reverseFirst_mean {index : Nat} {first second : Row}
    (firstCounted : first.coefficients.length = index)
    (secondCounted : second.coefficients.length = index + 1) (values : List Carrier) :
    (reverseFirst index first second).mean (swapAt index values) =
      add (add second.intercept (dot (second.coefficients.take index) values))
        (mul (pairSlope index second) (first.mean values)) := by
  have takeCounted : (second.coefficients.take index).length = index := by
    simp [secondCounted]
  show add (add second.intercept (mul (pairSlope index second) first.intercept))
      (dot (combine (pairSlope index second) (second.coefficients.take index) first.coefficients)
        (swapAt index values)) = _
  rw [dot_combine _ (by rw [takeCounted, firstCounted]), dot_swapAt_below
    (Nat.le_of_eq takeCounted),
    dot_swapAt_below (Nat.le_of_eq firstCounted)]
  unfold Row.mean
  real_grind

private theorem reverseSecond_mean {index : Nat} {first second : Row}
    (firstCounted : first.coefficients.length = index)
    (secondCounted : second.coefficients.length = index + 1) {values : List Carrier}
    (long : index + 1 < values.length) :
    (reverseSecond index first second).mean (swapAt index values) =
      add (first.mean values)
        (mul (pairGain first.variance second.variance (pairSlope index second))
          (sub (entry values (index + 1))
            (add (add second.intercept (dot (second.coefficients.take index) values))
              (mul (pairSlope index second) (first.mean values))))) := by
  have reversedCounted : (reverseFirst index first second).coefficients.length = index := by
    simp [reverseFirst, secondCounted, firstCounted]
  have combinedCounted : (combine (neg (pairGain first.variance second.variance
      (pairSlope index second))) first.coefficients
      (reverseFirst index first second).coefficients).length = index := by
    simp [firstCounted, reversedCounted]
  have firstMean := reverseFirst_mean firstCounted secondCounted values
  unfold Row.mean at firstMean
  rw [dot_swapAt_below (Nat.le_of_eq reversedCounted)] at firstMean
  show add (sub first.intercept (mul (pairGain first.variance second.variance
      (pairSlope index second)) (reverseFirst index first second).intercept))
      (dot (combine (neg (pairGain first.variance second.variance (pairSlope index second)))
        first.coefficients (reverseFirst index first second).coefficients ++
          [pairGain first.variance second.variance (pairSlope index second)])
        (swapAt index values)) = _
  rw [dot_concat combinedCounted, dot_combine _ (by rw [firstCounted, reversedCounted]),
    dot_swapAt_below (Nat.le_of_eq firstCounted), dot_swapAt_below (Nat.le_of_eq reversedCounted),
    entry_swapAt_left long]
  unfold Row.mean at *
  real_grind

/-- The two rebuilt conditionals at the swapped list multiply to the two old ones. -/
private theorem reverse_pair_density {index : Nat} {first second : Row}
    (firstPositive : lt zero first.variance) (secondPositive : lt zero second.variance)
    (firstCounted : first.coefficients.length = index)
    (secondCounted : second.coefficients.length = index + 1) {values : List Carrier}
    (long : index + 1 < values.length) :
    NNReal.mul ((reverseFirst index first second).density (swapAt index values) index)
        ((reverseSecond index first second).density (swapAt index values) (index + 1)) =
      NNReal.mul (first.density values index) (second.density values (index + 1)) := by
  unfold Row.density
  rw [reverseFirst_mean firstCounted secondCounted,
    reverseSecond_mean firstCounted secondCounted long,
    entry_swapAt_left long, entry_swapAt_right long, second_mean secondCounted]
  exact (density_reverse_pair firstPositive secondPositive (first.mean values)
    (add second.intercept (dot (second.coefficients.take index) values)) (pairSlope index second)
    (entry values index) (entry values (index + 1))).symm

/-- The reversed network's density at the swapped list is the old density. -/
public theorem Network.density_reverseAt (network : Network) (index : Nat)
    (values : List Carrier) :
    (network.reverseAt index).density (swapAt index values) = network.density values := by
  unfold Network.density
  rw [Network.length_reverseAt, swapAt_length]
  split
  · rename_i counted
    unfold Network.length at counted
    change conditionals (reverseRows index network.rows) 0 (swapAt index values) =
      conditionals network.rows 0 values
    by_cases long : index + 1 < network.rows.length
    · obtain ⟨front, first, second, back, split, frontCounted⟩ := rows_split long
      have triangular := network.triangular
      have positive := network.positive
      rw [split] at triangular positive counted ⊢
      obtain ⟨firstShape, secondShape, backShape⟩ := split_shape triangular frontCounted
      have valuesLong : index + 1 < values.length := by
        rw [counted]
        simp only [List.length_append, List.length_cons]
        omega
      have frontReads : ∀ position row, front[position]? = some row →
          row.coefficients.length ≤ index ∧ 0 + position < index := by
        intro position row found
        obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp found
        have shape := triangular position row (by rw [List.getElem?_append_left bounded]; exact
          found)
        exact ⟨by omega, by omega⟩
      have backReads : ∀ position row, back[position]? = some row →
          index + 1 < row.coefficients.length ∧ index + 1 < index + 1 + 1 + position := by
        intro position row found
        have shape := backShape position row found
        exact ⟨by omega, by omega⟩
      rw [reverseRows_split first second back frontCounted, conditionals_append_rows,
        conditionals_append_rows, conditionals_swap_front front 0 frontReads]
      congr 1
      rw [Nat.zero_add, frontCounted]
      simp only [conditionals]
      rw [← NNReal.mul_assoc, ← NNReal.mul_assoc,
        reverse_pair_density (positive first (by simp)) (positive second (by simp)) firstShape
          secondShape valuesLong,
        conditionals_swap_back back (index + 1 + 1) backReads valuesLong]
    · rw [reverseRows_short (by omega), swapAt_of_le (by omega)]
  · rfl

/-- Reversal: the law pushed along the swap of positions `i` and `i + 1` is the
law of the reversed network. When the network has no node `i + 1`, both sides
are its law. -/
public theorem Network.reverse (network : Network) (index : Nat) :
    network.law.map (swapAt index) (swapAt_measurable index) = (network.reverseAt index).law := by
  rw [network.law_eq_withDensity, (network.reverseAt index).law_eq_withDensity,
    Network.length_reverseAt]
  have pulled : (fun values => ENNReal.finite (network.density values)) =
      fun values => ENNReal.finite ((network.reverseAt index).density (swapAt index values)) := by
    funext values
    rw [Network.density_reverseAt]
  rw [pulled, Measure.map_withDensity _ _ (swapAt_measurable index)
    (network.reverseAt index).density_measurable, listVolume_swapAt]

public theorem permute_measurable (word : List Nat) :
    MeasurableMap (Space.list borel) (Space.list borel) (permute (α := Carrier) word) := by
  induction word with
  | nil =>
      intro set measurable
      exact measurable
  | cons index word induction =>
      intro set measurable
      exact swapAt_measurable index (induction measurable)

/-- Reverse along a word of adjacent swaps, left to right. -/
@[expose] public def Network.reverseAlong (network : Network) (word : List Nat) : Network :=
  word.foldl Network.reverseAt network

/-- The law pushed along a word of adjacent swaps is the law of the network
reversed along the same word. -/
public theorem Network.reverse_along (network : Network) (word : List Nat) :
    network.law.map (permute word) (permute_measurable word) = (network.reverseAlong word).law := by
  induction word generalizing network with
  | nil => exact Measure.map_id _
  | cons index word induction =>
      calc network.law.map (permute (index :: word)) (permute_measurable (index :: word))
          = (network.law.map (swapAt index) (swapAt_measurable index)).map (permute word)
              (permute_measurable word) := by
            rw [Measure.map_comp]
            rfl
        _ = (network.reverseAt index).law.map (permute word) (permute_measurable word) := by
            rw [network.reverse index]
        _ = (network.reverseAlong (index :: word)).law := induction (network.reverseAt index)

@[simp] public theorem Network.length_reverseAlong (network : Network) (word : List Nat) :
    (network.reverseAlong word).length = network.length := by
  induction word generalizing network with
  | nil => rfl
  | cons index word induction =>
      exact (induction (network.reverseAt index)).trans (network.length_reverseAt index)

/-- The density along a word of swaps, at the permuted list, is the old density. -/
public theorem Network.density_reverseAlong (network : Network) (word : List Nat)
    (values : List Carrier) :
    (network.reverseAlong word).density (permute word values) = network.density values := by
  induction word generalizing network values with
  | nil => rfl
  | cons index word induction =>
      exact (induction (network.reverseAt index) (swapAt index values)).trans
        (network.density_reverseAt index values)

/-! ### Moments of the pushed law -/

/-- The position that a swap of `i` and `i + 1` sends `k` to. -/
@[expose] public def swapIndex (index position : Nat) : Nat :=
  if position = index then index + 1 else if position = index + 1 then index else position

public theorem entry_swapAt {index : Nat} {values : List Carrier} (long : index + 1 < values.length)
    (position : Nat) : entry (swapAt index values) position = entry values (swapIndex index
      position) := by
  unfold swapIndex
  by_cases left : position = index
  · subst left
    rw [ite_eq_left rfl]
    exact entry_swapAt_left long
  · rw [ite_eq_right left]
    by_cases right : position = index + 1
    · subst right
      rw [ite_eq_left rfl]
      exact entry_swapAt_right long
    · rw [ite_eq_right right]
      rcases Nat.lt_or_ge position index with below | above
      · exact entry_swapAt_below below values
      · exact entry_swapAt_above (by omega) values

/-- The moments of the law pushed along a swap, read from the network's own
recurrences at the swapped positions. `reverse` equates this law with the
reversed network's, whose recurrences give the same moments unswapped. -/
public theorem Network.pushed_moments (network : Network) {index first second : Nat}
    (long : index + 1 < network.length) (firstBelow : swapIndex index first < network.length)
    (secondBelow : swapIndex index second < network.length) :
    HasRealIntegral (network.law.map (swapAt index) (swapAt_measurable index))
        (fun values => entry values first) (network.meanAt (swapIndex index first)) ∧
      HasRealIntegral (network.law.map (swapAt index) (swapAt_measurable index))
        (fun values => mul (entry values first) (entry values second))
        (add (network.covarianceAt (swapIndex index first) (swapIndex index second))
          (mul (network.meanAt (swapIndex index first)) (network.meanAt
            (swapIndex index second)))) := by
  obtain ⟨firstMoment, secondMoment⟩ := network.moments_eq firstBelow secondBelow
  constructor
  · apply HasRealIntegral.map (swapAt_measurable index) (entry_measurable first)
    refine HasRealIntegral.congr_ae firstMoment ?_ ?_
    · intro set measurable
      exact swapAt_measurable index (entry_measurable first measurable)
    · exact Measure.NullSet.mono network.law_length_null fun values different counted =>
        different (entry_swapAt (by omega) first).symm
  · have productMeasurable : MeasurableMap (Space.list borel) borel
        (fun values => mul (entry values first) (entry values second)) :=
      measurable_mul (entry_measurable first) (entry_measurable second)
    apply HasRealIntegral.map (swapAt_measurable index) productMeasurable
    refine HasRealIntegral.congr_ae secondMoment ?_ ?_
    · intro set measurable
      exact swapAt_measurable index (productMeasurable measurable)
    · exact Measure.NullSet.mono network.law_length_null fun values different counted =>
        different (by
          show _ = mul (entry (swapAt index values) first) (entry (swapAt index values) second)
          rw [entry_swapAt (by omega) first, entry_swapAt (by omega) second])

end
end Problib.Analysis.Gaussian
