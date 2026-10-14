module

public import Problib.Analysis.Gaussian.Network.Reverse
import Problib.Real.Grind

/-! A network from a mean and a covariance, by sequential regression.

Given a mean `m` and a covariance `Σ`, node `i` is the regression of `xᵢ` on
the earlier nodes. Its coefficients solve `Σ₍<i₎ bᵢ = σᵢ`, where `σᵢ` holds
`Σᵢⱼ` for `j < i`. Its innovation variance is the Schur complement
`dᵢ = Σᵢᵢ − ⟨σᵢ, bᵢ⟩`, and its intercept is `μᵢ = mᵢ − ⟨bᵢ, m₍<i₎⟩`
(`regressRow`). The system is solved through the prefix's own rows (`solve`):
the last unknown comes from the last row, and the earlier ones from the earlier
rows. So no matrix is inverted, and the coefficient rows are `B = I − L⁻¹` for
the unit lower factor `L` of `Σ = L D Lᵀ`, never `L`'s strict lower part.

A covariance has positive pivots (`PositivePivots`) when every Schur complement
is positive. Then `ofMoments m Σ` is a network, and its mean and covariance
recurrences return `m` and `Σ` (`ofMoments_mean`, `ofMoments_covariance`).
Regressing a network's own moments returns its rows (`regress_self`), so two
networks of one length with the same mean and covariance are equal (`unique`).
Everything here is finite real algebra over the recurrences of `Network.Basic`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Lists read by entry -/

public theorem entry_eq_getElem {values : List Carrier} {index : Nat} (below : index < values.length) :
    entry values index = values[index] := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]
  rfl

/-- Two lists of one length with equal entries are equal. -/
public theorem ext_entry {left right : List Carrier} (length : left.length = right.length)
    (equal : ∀ index, index < left.length → entry left index = entry right index) :
    left = right := by
  apply List.ext_getElem length
  intro index leftBelow rightBelow
  rw [← entry_eq_getElem leftBelow, ← entry_eq_getElem rightBelow]
  exact equal index leftBelow

public theorem entry_combine {scalar : Carrier} {left right : List Carrier} {index : Nat}
    (leftBelow : index < left.length) (rightBelow : index < right.length) :
    entry (combine scalar left right) index =
      add (entry left index) (mul scalar (entry right index)) := by
  unfold entry combine
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem leftBelow,
    List.getElem?_eq_getElem rightBelow]
  rfl

/-- A sum whose terms agree below its count reads equal entries. -/
public theorem dot_congr {coefficients left right : List Carrier}
    (equal : ∀ index, index < coefficients.length → entry left index = entry right index) :
    dot coefficients left = dot coefficients right := by
  rw [dot_eq_sumBelow, dot_eq_sumBelow]
  exact sumBelow_congr fun index below => by rw [equal index below]

/-- A positive value is nonzero. -/
public theorem ne_zero_of_positive {value : Carrier} (positive : lt zero value) : value ≠ zero :=
  fun vanished => lt_irrefl zero (vanished ▸ positive)

/-- Induction on a list by appending one entry at a time. -/
public theorem concat_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (concat : ∀ values value, motive values → motive (values ++ [value])) (values : List α) :
    motive values := by
  rw [← List.reverse_reverse values]
  induction values.reverse with
  | nil => exact nil
  | cons value rest induction =>
      rw [List.reverse_cons]
      exact concat _ _ induction

/-! ### Triangular lists of rows -/

public theorem triangular_concat {rows : List Row} {row : Row} :
    Triangular (rows ++ [row]) ↔ Triangular rows ∧ row.coefficients.length = rows.length := by
  constructor
  · intro triangular
    refine ⟨fun index current found => triangular index current ?_, triangular rows.length row ?_⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
      exact found
    · simp
  · rintro ⟨triangular, shaped⟩ index current found
    rcases Nat.lt_or_ge index rows.length with below | above
    · rw [List.getElem?_append_left below] at found
      exact triangular index current found
    · rw [List.getElem?_append_right above] at found
      rcases Nat.lt_or_ge (index - rows.length) 1 with first | beyond
      · have equal : index = rows.length := by omega
        rw [equal, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        rw [equal]
        exact shaped
      · rw [List.getElem?_eq_none (by simpa using beyond)] at found
        cases found

@[simp] public theorem Network.rows_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).rows = network.rows ++ [row] := rfl

/-! ### Solving through the rows -/

/-- Solve on rows listed last first. The last unknown is the last value's
residual on the last row, divided by its variance, and the earlier unknowns are
the earlier rows' solution less that multiple of the last row's coefficients. -/
@[expose] public def solveReversed : List Row → List Carrier → List Carrier
  | [], _ => []
  | row :: earlier, values =>
      let last := div (sub (entry values earlier.length) (dot row.coefficients values))
        row.variance
      combine (neg last) (solveReversed earlier values) row.coefficients ++ [last]

/-- The solution `x` of `C x = u`, where `C` is the covariance recurrence of
`rows`. It reads only the first `rows.length` values. -/
@[expose] public def solve (rows : List Row) (values : List Carrier) : List Carrier :=
  solveReversed rows.reverse values

/-- The last unknown of `solve (rows ++ [row])`. -/
@[expose] public def solveLast (rows : List Row) (row : Row) (values : List Carrier) : Carrier :=
  div (sub (entry values rows.length) (dot row.coefficients values)) row.variance

@[simp] public theorem solve_nil (values : List Carrier) : solve [] values = [] := rfl

public theorem solve_concat (rows : List Row) (row : Row) (values : List Carrier) :
    solve (rows ++ [row]) values =
      combine (neg (solveLast rows row values)) (solve rows values) row.coefficients ++
        [solveLast rows row values] := by
  simp only [solve, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, solveReversed, solveLast, List.length_reverse]

public theorem solve_length {rows : List Row} (triangular : Triangular rows)
    (values : List Carrier) : (solve rows values).length = rows.length := by
  induction rows using concat_induction with
  | nil => rfl
  | concat rows row induction =>
      obtain ⟨front, shaped⟩ := triangular_concat.mp triangular
      rw [solve_concat, List.length_append, combine_length, induction front, shaped]
      simp

/-- `solve` reads only the first `rows.length` values. -/
public theorem solve_congr {rows : List Row} (triangular : Triangular rows)
    {left right : List Carrier}
    (equal : ∀ index, index < rows.length → entry left index = entry right index) :
    solve rows left = solve rows right := by
  induction rows using concat_induction with
  | nil => rfl
  | concat rows row induction =>
      obtain ⟨front, shaped⟩ := triangular_concat.mp triangular
      have below : ∀ index, index < rows.length → entry left index = entry right index :=
        fun index inside => equal index (by simp; omega)
      have last : solveLast rows row left = solveLast rows row right := by
        unfold solveLast
        rw [equal rows.length (by simp), dot_congr (fun index inside => below index
          (by rw [← shaped]; exact inside))]
      rw [solve_concat, solve_concat, induction front below, last]

/-- `solve` reads only the rows' coefficients and variances. -/
public theorem solve_congr_rows {left right : List Row}
    (coefficients : left.map Row.coefficients = right.map Row.coefficients)
    (variance : left.map Row.variance = right.map Row.variance) (values : List Carrier) :
    solve left values = solve right values := by
  unfold solve
  have reversedCoefficients : left.reverse.map Row.coefficients =
      right.reverse.map Row.coefficients := by
    rw [List.map_reverse, List.map_reverse, coefficients]
  have reversedVariance : left.reverse.map Row.variance = right.reverse.map Row.variance := by
    rw [List.map_reverse, List.map_reverse, variance]
  generalize left.reverse = left at reversedCoefficients reversedVariance
  generalize right.reverse = right at reversedCoefficients reversedVariance
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => cases reversedCoefficients
  | cons row earlier induction =>
      cases right with
      | nil => cases reversedCoefficients
      | cons other others =>
          simp only [List.map_cons, List.cons.injEq] at reversedCoefficients reversedVariance
          have length : earlier.length = others.length := by
            simpa using congrArg List.length reversedCoefficients.2
          simp only [solveReversed, induction others reversedCoefficients.2 reversedVariance.2,
            reversedCoefficients.1, reversedVariance.1, length]

/-! ### The covariance recurrence applied to a list -/

/-- `(C x)ₖ = Σ_{l<n} Cₖₗ xₗ`, with `C` the covariance recurrence. -/
@[expose] public def Network.act (network : Network) (values : List Carrier) (index : Nat) :
    Carrier :=
  sumBelow network.length (fun other =>
    mul (network.covarianceAt index other) (entry values other))

public theorem Network.act_congr (network : Network) {left right : List Carrier}
    (equal : ∀ index, index < network.length → entry left index = entry right index)
    (index : Nat) : network.act left index = network.act right index :=
  sumBelow_congr fun other below => by rw [equal other below]

public theorem Network.act_combine (network : Network) (scalar : Carrier)
    {left right : List Carrier} (leftLength : left.length = network.length)
    (rightLength : right.length = network.length) (index : Nat) :
    network.act (combine scalar left right) index =
      add (network.act left index) (mul scalar (network.act right index)) := by
  unfold Network.act
  rw [← sumBelow_mul_left, ← sumBelow_add]
  apply sumBelow_congr
  intro other below
  rw [entry_combine (by omega) (by omega)]
  real_grind

/-- `xᵀ C z = zᵀ C x`, by the symmetry of the covariance recurrence. -/
public theorem Network.act_comm (network : Network) (left right : List Carrier) :
    sumBelow network.length (fun index => mul (network.act left index) (entry right index)) =
      sumBelow network.length (fun index => mul (entry left index) (network.act right index)) := by
  unfold Network.act
  have expand : ∀ (count : Nat) (scalar : Carrier) (term : Nat → Carrier),
      mul (sumBelow count term) scalar = sumBelow count (fun index => mul (term index) scalar) := by
    intro count scalar term
    rw [mul_comm, ← sumBelow_mul_left]
    exact sumBelow_congr fun _ _ => mul_comm _ _
  simp only [expand, ← sumBelow_mul_left]
  rw [sumBelow_swap]
  apply sumBelow_congr
  intro first firstBelow
  apply sumBelow_congr
  intro second secondBelow
  rw [network.covarianceAt_symmetric secondBelow firstBelow]
  real_grind

section Append

variable (network : Network) (row : Row) (shaped : row.coefficients.length = network.length)
  (positive : lt zero row.variance)

include shaped in
public theorem Network.act_append_below (values : List Carrier) {index : Nat}
    (below : index < network.length) :
    (network.append row shaped positive).act values index =
      add (network.act values index)
        (mul (network.cross row index) (entry values network.length)) := by
  unfold Network.act
  rw [Network.length_append]
  change add (sumBelow network.length _) _ = _
  dsimp only
  rw [Network.covarianceAt_append_right _ _ shaped _ below]
  congr 1
  exact sumBelow_congr fun other otherBelow => by
    rw [Network.covarianceAt_append_below _ _ shaped _ below otherBelow]

include shaped in
public theorem Network.act_append_last (values : List Carrier) :
    (network.append row shaped positive).act values network.length =
      add (sumBelow network.length (fun index =>
          mul (network.cross row index) (entry values index)))
        (mul (add (sumBelow network.length (fun index =>
            mul (entry row.coefficients index) (network.cross row index))) row.variance)
          (entry values network.length)) := by
  unfold Network.act
  rw [Network.length_append]
  change add (sumBelow network.length _) _ = _
  dsimp only
  rw [Network.covarianceAt_append_corner _ _ shaped]
  congr 1
  exact sumBelow_congr fun other otherBelow => by
    rw [Network.covarianceAt_append_bottom _ _ shaped _ otherBelow]

end Append

/-- `C (solve u) = u` below the network's length. -/
public theorem Network.act_solve (network : Network) (values : List Carrier) {index : Nat}
    (below : index < network.length) :
    network.act (solve network.rows values) index = entry values index := by
  induction network using Network.induction generalizing index with
  | empty network empty =>
      have zero : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      omega
  | append network row shaped positive induction =>
      rw [Network.length_append] at below
      have solved : (solve network.rows values).length = network.length :=
        solve_length network.triangular values
      rw [Network.rows_append, solve_concat]
      have cancel : mul row.variance (solveLast network.rows row values) =
          sub (entry values network.length) (dot row.coefficients values) :=
        mul_div_cancel _ (ne_zero_of_positive positive)
      generalize solveLast network.rows row values = last at cancel ⊢
      generalize frontDefinition :
        combine (neg last) (solve network.rows values) row.coefficients = front
      have frontLength : front.length = network.length := by
        rw [← frontDefinition, combine_length, solved, shaped, Nat.min_self]
      have frontEntry : ∀ other, other < network.length →
          entry (front ++ [last]) other =
            entry (combine (neg last) (solve network.rows values) row.coefficients) other :=
        fun other otherBelow => by
          rw [entry_append_left _ (by rw [frontLength]; exact otherBelow), frontDefinition]
      have lastEntry : entry (front ++ [last]) network.length = last := by
        rw [← frontLength]
        exact entry_concat_length front last
      rcases Nat.lt_or_ge index network.length with inside | outside
      · rw [Network.act_append_below _ _ shaped _ _ inside, lastEntry,
          network.act_congr frontEntry, network.act_combine _ solved shaped,
          induction inside]
        unfold Network.cross
        change add (add _ (mul _ (network.act row.coefficients index))) (mul
          (network.act row.coefficients index) last) = _
        real_grind
      · have last_index : index = network.length := by omega
        subst last_index
        rw [Network.act_append_last _ _ shaped, lastEntry]
        have crossed : sumBelow network.length (fun other =>
            mul (network.cross row other) (entry (front ++ [last]) other)) =
            add (dot row.coefficients values)
              (mul (neg last) (sumBelow network.length (fun other =>
                mul (entry row.coefficients other) (network.cross row other)))) := by
          rw [sumBelow_congr fun other otherBelow => by rw [frontEntry other otherBelow,
            entry_combine (by omega) (by omega)]]
          have split : ∀ other, mul (network.cross row other)
              (add (entry (solve network.rows values) other)
                (mul (neg last) (entry row.coefficients other))) =
              add (mul (network.act row.coefficients other)
                (entry (solve network.rows values) other))
                (mul (neg last) (mul (entry row.coefficients other)
                  (network.cross row other))) := fun other => by
            change mul (network.act row.coefficients other) _ =
              add _ (mul _ (mul _ (network.act row.coefficients other)))
            generalize network.act row.coefficients other = crossed
            real_grind
          rw [sumBelow_congr fun other _ => split other, sumBelow_add, sumBelow_mul_left,
            network.act_comm, dot_eq_sumBelow, shaped]
          congr 1
          exact sumBelow_congr fun other otherBelow => by rw [induction otherBelow]
        rw [crossed]
        real_grind

/-- `solve (C x) = x`: the solve inverts the covariance recurrence. -/
public theorem Network.solve_act (network : Network) {solution values : List Carrier}
    (length : solution.length = network.length)
    (applied : ∀ index, index < network.length → entry values index = network.act solution index) :
    solve network.rows values = solution := by
  induction network using Network.induction generalizing solution values with
  | empty network empty =>
      have zero : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      rw [empty]
      exact (List.length_eq_zero_iff.mp (length.trans zero)).symm
  | append network row shaped positive induction =>
      rw [Network.length_append] at length
      generalize frontDefinition : solution.take network.length = front
      generalize topDefinition : entry solution network.length = top
      have frontLength : front.length = network.length := by
        rw [← frontDefinition, List.length_take, length]
        omega
      have frontEntry : ∀ other, other < network.length → entry solution other = entry front other :=
        fun other otherBelow => by rw [← frontDefinition, entry_take otherBelow solution]
      have frontAct : ∀ index, network.act solution index = network.act front index :=
        network.act_congr frontEntry
      -- The earlier values are `C' (x' + t b)`.
      have earlier : solve network.rows values = combine top front row.coefficients := by
        apply induction (by simp [combine_length, frontLength, shaped])
        intro index below
        rw [applied index (by rw [Network.length_append]; omega),
          Network.act_append_below _ _ shaped _ _ below, network.act_combine _ frontLength shaped,
          frontAct, topDefinition]
        change add _ (mul (network.act row.coefficients index) top) = _
        real_grind
      -- The last unknown is `t`.
      have lastValue : solveLast network.rows row values = top := by
        have residual : sub (entry values network.length) (dot row.coefficients values) =
            mul row.variance top := by
          rw [applied network.length (by rw [Network.length_append]; omega),
            Network.act_append_last _ _ shaped, dot_eq_sumBelow, shaped]
          have readings : sumBelow network.length (fun index =>
              mul (entry row.coefficients index) (entry values index)) =
              add (sumBelow network.length (fun index =>
                mul (network.cross row index) (entry solution index)))
                (mul top (sumBelow network.length (fun index =>
                  mul (entry row.coefficients index) (network.cross row index)))) := by
            rw [sumBelow_congr fun index below => by
              rw [applied index (by rw [Network.length_append]; omega),
                Network.act_append_below _ _ shaped _ _ below]]
            have split : ∀ index, mul (entry row.coefficients index)
                (add (network.act solution index)
                  (mul (network.cross row index) (entry solution network.length))) =
                add (mul (entry row.coefficients index) (network.act solution index))
                  (mul top (mul (entry row.coefficients index) (network.cross row index))) :=
              fun index => by real_grind
            rw [sumBelow_congr fun index _ => split index, sumBelow_add, sumBelow_mul_left,
              ← network.act_comm]
            rfl
          rw [readings]
          real_grind
        unfold solveLast
        change div (sub (entry values network.length) _) _ = _
        rw [residual, mul_comm]
        unfold div
        rw [mul_assoc, mul_inverse_cancel (ne_zero_of_positive positive), mul_one]
      rw [Network.rows_append, solve_concat, earlier, lastValue]
      apply ext_entry (by simp [combine_length, frontLength, shaped, length])
      intro index below
      simp only [List.length_append, combine_length, frontLength, shaped, Nat.min_self,
        List.length_singleton] at below
      rcases Nat.lt_or_ge index network.length with inside | outside
      · rw [entry_append_left _ (by simp [combine_length, frontLength, shaped]; exact inside),
          entry_combine (by simp [combine_length, frontLength, shaped]; exact inside)
            (by omega),
          entry_combine (by omega) (by omega), frontEntry index inside]
        real_grind
      · have last_index : index = network.length := by omega
        subst last_index
        have counted : (combine (neg top) (combine top front row.coefficients)
            row.coefficients).length = network.length := by
          simp [combine_length, frontLength, shaped]
        rw [← counted, entry_concat_length, counted, topDefinition]

/-! ### Sequential regression -/

/-- Node `i`'s regression on the earlier rows, read from row `i` of the
covariance and from the mean: `b = solve rows σᵢ`, `μᵢ = mᵢ − ⟨b, m⟩` and
`dᵢ = Σᵢᵢ − ⟨b, σᵢ⟩`. Each sum reads only the first `i` entries. -/
@[expose] public def regressRow (mean : List Carrier) (rows : List Row) (row : List Carrier) :
    Row where
  intercept := sub (entry mean rows.length) (dot (solve rows row) mean)
  coefficients := solve rows row
  variance := sub (entry row rows.length) (dot (solve rows row) row)

/-- The regression rows of a covariance, as a left fold over its rows. -/
@[expose] public def regress (mean : List Carrier) (covariance : List (List Carrier)) :
    List Row :=
  covariance.foldl (fun rows row => rows ++ [regressRow mean rows row]) []

@[simp] public theorem regress_nil (mean : List Carrier) : regress mean [] = [] := rfl

public theorem regress_concat (mean : List Carrier) (covariance : List (List Carrier))
    (row : List Carrier) :
    regress mean (covariance ++ [row]) =
      regress mean covariance ++ [regressRow mean (regress mean covariance) row] := by
  simp [regress, List.foldl_append]

@[simp] public theorem regress_length (mean : List Carrier) (covariance : List (List Carrier)) :
    (regress mean covariance).length = covariance.length := by
  induction covariance using concat_induction with
  | nil => rfl
  | concat covariance row induction => simp [regress_concat, induction]

public theorem regress_triangular (mean : List Carrier) (covariance : List (List Carrier)) :
    Triangular (regress mean covariance) := by
  induction covariance using concat_induction with
  | nil => intro index row found; simp at found
  | concat covariance row induction =>
      rw [regress_concat]
      exact triangular_concat.mpr ⟨induction, solve_length induction row⟩

/-- The coefficients and variances do not read the mean. -/
public theorem regress_shape (left right : List Carrier) (covariance : List (List Carrier)) :
    (regress left covariance).map Row.coefficients = (regress right covariance).map Row.coefficients ∧
      (regress left covariance).map Row.variance = (regress right covariance).map Row.variance := by
  induction covariance using concat_induction with
  | nil => exact ⟨rfl, rfl⟩
  | concat covariance row induction =>
      have solved := solve_congr_rows induction.1 induction.2 row
      have length : (regress left covariance).length = (regress right covariance).length := by simp
      simp only [regress_concat, List.map_append, List.map_cons, List.map_nil, regressRow, solved,
        length]
      exact ⟨congrArg (· ++ _) induction.1, congrArg (· ++ _) induction.2⟩

/-- `regress` reads only `mᵢ` and `Σᵢⱼ` for `j ≤ i`. -/
public theorem regress_congr {leftMean rightMean : List Carrier}
    {left right : List (List Carrier)} (length : left.length = right.length)
    (mean : ∀ index, index < left.length → entry leftMean index = entry rightMean index)
    (lower : ∀ first second, second ≤ first → first < left.length →
      entry (left.getD first []) second = entry (right.getD first []) second) :
    regress leftMean left = regress rightMean right := by
  induction left using concat_induction generalizing right with
  | nil =>
      rw [List.length_eq_zero_iff.mp length.symm]
      rfl
  | concat left row induction =>
      obtain ⟨right, other, rfl⟩ : ∃ front last, right = front ++ [last] := by
        rcases List.eq_nil_or_concat right with empty | ⟨front, last, split⟩
        · subst empty
          simp at length
        · exact ⟨front, last, by rw [split, List.concat_eq_append]⟩
      simp only [List.length_append, List.length_singleton] at length mean lower
      have counted : left.length = right.length := by omega
      have earlier : regress leftMean left = regress rightMean right := by
        apply induction counted (fun index below => mean index (by omega))
        intro first second ordered below
        have value := lower first second ordered (by omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left below,
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD] at value
      have lastRow : ∀ second, second ≤ left.length → entry row second = entry other second := by
        intro second ordered
        have value := lower left.length second ordered (by omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          show left.length - right.length = 0 by omega] at value
      rw [regress_concat, regress_concat, earlier]
      have triangular := regress_triangular rightMean right
      have rowsLength : (regress rightMean right).length = left.length := by simp [counted]
      have solved : solve (regress rightMean right) row = solve (regress rightMean right) other :=
        solve_congr triangular fun index below => lastRow index (by omega)
      have solvedLength : (solve (regress rightMean right) other).length = left.length := by
        rw [solve_length triangular, rowsLength]
      congr 2
      simp only [regressRow, solved, rowsLength]
      rw [mean left.length (by omega), lastRow left.length (Nat.le_refl _),
        dot_congr (left := leftMean) (right := rightMean) fun index below =>
          mean index (by omega),
        dot_congr (left := row) (right := other) fun index below =>
          lastRow index (by omega)]

/-- Every Schur complement of the covariance is positive. -/
@[expose] public def PositivePivots (covariance : List (List Carrier)) : Prop :=
  ∀ row ∈ regress [] covariance, lt zero row.variance

public theorem regress_positive {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) (mean : List Carrier) :
    ∀ row ∈ regress mean covariance, lt zero row.variance := by
  intro row member
  have mapped : row.variance ∈ (regress [] covariance).map Row.variance := by
    rw [← (regress_shape mean [] covariance).2]
    exact List.mem_map_of_mem member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp mapped
  rw [← same]
  exact positive original originalMember

/-- The network of a mean and a covariance with positive pivots, by
sequential regression. -/
@[expose] public def ofMoments (mean : List Carrier) (covariance : List (List Carrier))
    (positive : PositivePivots covariance) : Network where
  rows := regress mean covariance
  triangular := regress_triangular mean covariance
  positive := regress_positive positive mean

@[simp] public theorem ofMoments_length (mean : List Carrier) (covariance : List (List Carrier))
    (positive : PositivePivots covariance) :
    (ofMoments mean covariance positive).length = covariance.length :=
  regress_length mean covariance

/-- A covariance whose leading block is symmetric. Rows may be longer than the
covariance has rows: only the leading square block is read. -/
@[expose] public def Symmetric (covariance : List (List Carrier)) : Prop :=
  ∀ first second, first < covariance.length → second < covariance.length →
    entry (covariance.getD first []) second = entry (covariance.getD second []) first

/-- Every row has as many entries as there are rows. -/
@[expose] public def Square (covariance : List (List Carrier)) : Prop :=
  ∀ row ∈ covariance, row.length = covariance.length

public theorem getD_append_left {front : List (List Carrier)} (back : List (List Carrier))
    {index : Nat} (below : index < front.length) :
    (front ++ back).getD index [] = front.getD index [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left below, ← List.getD_eq_getElem?_getD]

public theorem getD_concat_length (front : List (List Carrier)) (row : List Carrier) :
    (front ++ [row]).getD front.length [] = row := by
  simp

/-- A network whose rows are the regression of `m` and `Σ` has mean `m` and
covariance `Σ` on `Σ`'s leading block. -/
public theorem regress_moments {mean : List Carrier} {covariance : List (List Carrier)}
    (symmetric : Symmetric covariance) (network : Network)
    (rows : network.rows = regress mean covariance) :
    (∀ index, index < covariance.length → network.meanAt index = entry mean index) ∧
      ∀ first second, first < covariance.length → second < covariance.length →
        network.covarianceAt first second = entry (covariance.getD first []) second := by
  induction covariance using concat_induction generalizing network with
  | nil =>
      exact ⟨fun _ below => absurd below (Nat.not_lt_zero _),
        fun _ _ below => absurd below (Nat.not_lt_zero _)⟩
  | concat covariance row induction =>
      rw [regress_concat] at rows
      have prefixSymmetric : Symmetric covariance := by
        intro first second firstBelow secondBelow
        have value := symmetric first second (by simp; omega) (by simp; omega)
        rwa [getD_append_left _ firstBelow, getD_append_left _ secondBelow] at value
      let earlier : Network := {
        rows := regress mean covariance
        triangular := regress_triangular mean covariance
        positive := fun current member => network.positive current (by
          rw [rows]
          exact List.mem_append_left _ member) }
      have earlierLength : earlier.length = covariance.length := regress_length mean covariance
      have shaped : (regressRow mean (regress mean covariance) row).coefficients.length =
          earlier.length := solve_length (regress_triangular mean covariance) row
      have rebuilt : network = earlier.append (regressRow mean (regress mean covariance) row) shaped
          (network.positive _ (by rw [rows]; simp)) := Network.ext rows
      obtain ⟨earlierMean, earlierCovariance⟩ := induction prefixSymmetric earlier rfl
      rw [rebuilt]
      -- The regression's coefficients solve `C b = σ`.
      have solved : ∀ index, index < earlier.length →
          earlier.cross (regressRow mean (regress mean covariance) row) index = entry row index :=
        fun index below => earlier.act_solve row below
      have readRow : (covariance ++ [row]).getD covariance.length [] = row :=
        getD_concat_length covariance row
      have entryBelow : ∀ first second, first < covariance.length →
          entry ((covariance ++ [row]).getD first []) second = entry (covariance.getD first []) second :=
        fun first second below => by rw [getD_append_left _ below]
      simp only [List.length_append, List.length_singleton]
      constructor
      · intro index below
        rcases Nat.lt_or_ge index covariance.length with inside | outside
        · rw [Network.meanAt_append_below _ _ shaped _ (by omega), earlierMean index inside]
        · have last : index = earlier.length := by omega
          subst last
          rw [Network.meanAt_append_last _ _ shaped]
          change add (sub (entry mean (regress mean covariance).length) (dot (solve _ row) mean))
            _ = _
          rw [regress_length, ← earlierLength, dot_eq_sumBelow,
            solve_length (regress_triangular mean covariance)]
          have means : sumBelow earlier.length (fun other =>
              mul (entry (solve (regress mean covariance) row) other) (earlier.meanAt other)) =
              sumBelow earlier.length (fun other =>
                mul (entry (solve (regress mean covariance) row) other) (entry mean other)) :=
            sumBelow_congr fun other otherBelow => by rw [earlierMean other (by omega)]
          change add (sub _ (sumBelow earlier.length _)) (sumBelow earlier.length (fun other =>
            mul (entry (solve (regress mean covariance) row) other) (earlier.meanAt other))) = _
          rw [means]
          real_grind
      · intro first second firstBelow secondBelow
        rcases Nat.lt_or_ge first covariance.length with firstInside | firstOutside <;>
          rcases Nat.lt_or_ge second covariance.length with secondInside | secondOutside
        · rw [Network.covarianceAt_append_below _ _ shaped _ (by omega) (by omega),
            earlierCovariance first second firstInside secondInside, entryBelow _ _ firstInside]
        · have last : second = earlier.length := by omega
          subst last
          rw [Network.covarianceAt_append_right _ _ shaped _ (by omega), solved first (by omega),
            entryBelow _ _ firstInside, earlierLength]
          have value := symmetric first covariance.length (by simp; omega) (by simp)
          rw [entryBelow _ _ firstInside, readRow] at value
          exact value.symm
        · have last : first = earlier.length := by omega
          subst last
          rw [Network.covarianceAt_append_bottom _ _ shaped _ (by omega), solved second (by omega),
            earlierLength, readRow]
        · have firstLast : first = earlier.length := by omega
          have secondLast : second = earlier.length := by omega
          subst firstLast
          subst secondLast
          rw [Network.covarianceAt_append_corner _ _ shaped, earlierLength, readRow]
          change add _ (sub (entry row (regress mean covariance).length)
            (dot (solve (regress mean covariance) row) row)) = _
          rw [regress_length, dot_eq_sumBelow, solve_length (regress_triangular mean covariance),
            regress_length]
          rw [sumBelow_congr (count := covariance.length) fun other otherBelow => by
            rw [solved other (by rw [earlierLength]; exact otherBelow)]]
          change add (sumBelow covariance.length (fun other =>
            mul (entry (solve (regress mean covariance) row) other) (entry row other))) _ = _
          real_grind

public theorem ofMoments_meanAt {mean : List Carrier} {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) (symmetric : Symmetric covariance) {index : Nat}
    (below : index < covariance.length) :
    (ofMoments mean covariance positive).meanAt index = entry mean index :=
  (regress_moments symmetric _ rfl).1 index below

public theorem ofMoments_covarianceAt {mean : List Carrier} {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) (symmetric : Symmetric covariance) {first second : Nat}
    (firstBelow : first < covariance.length) (secondBelow : second < covariance.length) :
    (ofMoments mean covariance positive).covarianceAt first second =
      entry (covariance.getD first []) second :=
  (regress_moments symmetric _ rfl).2 first second firstBelow secondBelow

/-- The mean recurrence of `ofMoments m Σ` is `m`. -/
public theorem ofMoments_mean {mean : List Carrier} {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) (symmetric : Symmetric covariance)
    (meanLength : mean.length = covariance.length) :
    (ofMoments mean covariance positive).mean = mean := by
  have shape := (ofMoments mean covariance positive).shape
  rw [ofMoments_length] at shape
  apply ext_entry (shape.1.trans meanLength.symm)
  intro index below
  exact ofMoments_meanAt positive symmetric (by omega)

/-- The covariance recurrence of `ofMoments m Σ` is `Σ`. -/
public theorem ofMoments_covariance {mean : List Carrier} {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) (symmetric : Symmetric covariance)
    (square : Square covariance) :
    (ofMoments mean covariance positive).covariance = covariance := by
  have shape := (ofMoments mean covariance positive).shape
  rw [ofMoments_length] at shape
  apply List.ext_getElem shape.2.1
  intro first leftBelow rightBelow
  have leftRow : (ofMoments mean covariance positive).covariance.getD first [] =
      (ofMoments mean covariance positive).covariance[first] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem leftBelow]
    rfl
  have rightRow : covariance.getD first [] = covariance[first] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rightBelow]
    rfl
  apply ext_entry
  · rw [shape.2.2 _ (List.getElem_mem leftBelow), square _ (List.getElem_mem rightBelow)]
  · intro second secondBelow
    rw [shape.2.2 _ (List.getElem_mem leftBelow)] at secondBelow
    have value := ofMoments_covarianceAt (mean := mean) positive symmetric rightBelow secondBelow
    unfold Network.covarianceAt at value
    rwa [leftRow, rightRow] at value

/-! ### Regressing a network's own moments -/

/-- Regressing a network's mean and covariance returns its rows. -/
public theorem Network.regress_self (network : Network) :
    regress network.mean network.covariance = network.rows := by
  induction network using Network.induction with
  | empty network empty =>
      have zero : network.covariance = [] := by
        unfold Network.covariance
        rw [empty]
        rfl
      rw [zero, empty]
      rfl
  | append network row shaped positive induction =>
      have shape := (network.append row shaped positive).shape
      rw [Network.length_append] at shape
      obtain ⟨front, last, split⟩ := (List.eq_nil_or_concat
        (network.append row shaped positive).covariance).resolve_left (by
          intro empty
          have := shape.2.1
          rw [empty] at this
          cases this)
      rw [List.concat_eq_append] at split
      have frontLength : front.length = network.length := by
        have := shape.2.1
        rw [split, List.length_append, List.length_singleton] at this
        omega
      have readFront : ∀ first, first < network.length →
          (network.append row shaped positive).covariance.getD first [] = front.getD first [] :=
        fun first below => by rw [split, getD_append_left _ (by omega)]
      have readLast : (network.append row shaped positive).covariance.getD network.length [] =
          last := by rw [split, ← frontLength, getD_concat_length]
      rw [split, regress_concat]
      have earlier : regress (network.append row shaped positive).mean front =
          regress network.mean network.covariance := by
        apply regress_congr (by rw [frontLength, network.shape.2.1])
        · intro index below
          rw [frontLength] at below
          exact network.meanAt_append_below row shaped positive below
        · intro first second ordered below
          rw [frontLength] at below
          have value := network.covarianceAt_append_below row shaped positive
            (first := first) (second := second) below (by omega)
          unfold Network.covarianceAt at value
          rwa [readFront first below] at value
      rw [earlier, induction, Network.rows_append]
      congr 1
      have lastEntry : ∀ index, entry last index =
          (network.append row shaped positive).covarianceAt network.length index :=
        fun index => by unfold Network.covarianceAt; rw [readLast]
      have coefficients : solve network.rows last = row.coefficients := by
        apply network.solve_act shaped
        intro index below
        rw [lastEntry, Network.covarianceAt_append_bottom _ _ shaped _ below]
        rfl
      have sameLength : network.rows.length = network.length := rfl
      cases row with
      | mk intercept rowCoefficients variance =>
      simp only at shaped coefficients
      simp only [regressRow, coefficients, sameLength, List.cons.injEq, and_true]
      congr 1
      · have meanLast := network.meanAt_append_last ⟨intercept, rowCoefficients, variance⟩ shaped
          positive
        unfold Network.meanAt at meanLast
        rw [meanLast, dot_eq_sumBelow, shaped]
        have means : sumBelow network.length (fun index => mul (entry rowCoefficients index)
            (entry (network.append ⟨intercept, rowCoefficients, variance⟩ shaped positive).mean
              index)) =
            sumBelow network.length (fun index =>
              mul (entry rowCoefficients index) (network.meanAt index)) :=
          sumBelow_congr fun index below => by
            rw [← Network.meanAt, network.meanAt_append_below _ shaped positive below]
        rw [means]
        unfold Network.meanAt
        real_grind
      · rw [lastEntry, Network.covarianceAt_append_corner _ _ shaped, dot_eq_sumBelow, shaped]
        have reads : sumBelow network.length (fun index =>
            mul (entry rowCoefficients index) (entry last index)) =
            sumBelow network.length (fun index => mul (entry rowCoefficients index)
              (network.cross ⟨intercept, rowCoefficients, variance⟩ index)) :=
          sumBelow_congr fun index below => by
            rw [lastEntry, Network.covarianceAt_append_bottom _ _ shaped _ below]
        rw [reads]
        real_grind

/-- A network's covariance recurrence has positive pivots. -/
public theorem Network.positivePivots (network : Network) : PositivePivots network.covariance :=
  fun row member => by
    have mapped : row.variance ∈ network.rows.map Row.variance := by
      rw [← network.regress_self, (regress_shape network.mean [] network.covariance).2]
      exact List.mem_map_of_mem member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp mapped
    rw [← same]
    exact network.positive original originalMember

/-- `ofMoments` of a network's own moments is the network. -/
public theorem Network.ofMoments_self (network : Network) :
    ofMoments network.mean network.covariance network.positivePivots = network :=
  Network.ext network.regress_self

/-- Fixed-order uniqueness: two networks of one length with the same mean and
covariance recurrences are equal. -/
public theorem Network.unique {left right : Network} (length : left.length = right.length)
    (mean : ∀ index, index < left.length → left.meanAt index = right.meanAt index)
    (covariance : ∀ first second, first < left.length → second < left.length →
      left.covarianceAt first second = right.covarianceAt first second) :
    left = right := by
  apply Network.ext
  rw [← left.regress_self, ← right.regress_self]
  apply regress_congr (by rw [left.shape.2.1, right.shape.2.1, length])
  · intro index below
    rw [left.shape.2.1] at below
    exact mean index below
  · intro first second ordered below
    rw [left.shape.2.1] at below
    exact covariance first second below (by omega)

end
end Problib.Analysis.Gaussian
