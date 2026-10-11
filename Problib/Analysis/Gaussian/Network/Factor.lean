module

public import Problib.Analysis.Gaussian.Network.Moments
import Problib.Real.Grind

/-! The exact factorization of a runtime covariance, with typed results.

A field is given at run time as a mean `m` and a covariance `Σ`, each a list.
Not every such pair is a covariance with a density, so `factor m Σ` answers a
`FieldResult` that names what it found:

- `shape k`: row `k` does not have one entry per row, or `k = n` and the mean
  does not have `n` entries.
- `asymmetric i j`: `Σᵢⱼ ≠ Σⱼᵢ` with `j < i`, so `Σ` is not a covariance.
- `pivot k v`: the first Schur complement `v ≤ 0` is at row `k`. Then `Σ` is not
  positive definite (`factor_pivot`), so the positive-definite route is
  unavailable. That holds for an indefinite `Σ` and for a singular
  semidefinite one, and neither is called a missing law.
- `numerical k`: reserved for native execution, where a pivot can be
  nonpositive, NaN or infinite in floating point. The exact factorization never
  answers it (`factor_ne_numerical`). It certifies nothing about the exact `Σ`,
  as a computed positive pivot does not, and a consumer reads it as no answer.
- `network N`: success. `N`'s mean and covariance recurrences are `m` and `Σ`
  (`factor_sound`).

After the shape and symmetry passes, the rows are folded left (`factorStep`).
The state is the accepted prefix of regression rows, every one with a positive
variance. Each step regresses the next row on that prefix (`regressRow`), which
divides only by accepted variances, and appends it only on the positive branch
of its pivot. No square root is taken. Nothing adds jitter, clamps a pivot or
symmetrizes. Every square, symmetric, positive-definite `Σ` answers `network`
(`factor_complete`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- Entry `(i, j)` of a matrix given as its list of rows, zero when absent. -/
@[expose] public def matrixEntry (matrix : List (List Carrier)) (first second : Nat) : Carrier :=
  entry (matrix.getD first []) second

/-- Positive definiteness: every coefficient vector that is nonzero below `n`
has a positive quadratic form. -/
@[expose] public def PositiveDefinite (covariance : List (List Carrier)) : Prop :=
  ∀ coefficient : Nat → Carrier,
    (∃ index, index < covariance.length ∧ coefficient index ≠ zero) →
      lt zero (quadratic covariance.length coefficient (matrixEntry covariance))

/-! ### The shape pass -/

/-- The first position, counted from `start`, of a row whose length is not
`count`. -/
@[expose] public def raggedFrom (count : Nat) : Nat → List (List Carrier) → Option Nat
  | _, [] => none
  | start, row :: rows => if row.length = count then raggedFrom count (start + 1) rows else some start

public theorem raggedFrom_none {count start : Nat} {rows : List (List Carrier)}
    (none : raggedFrom count start rows = Option.none) : ∀ row ∈ rows, row.length = count := by
  induction rows generalizing start with
  | nil => intro row member; cases member
  | cons first rest induction =>
      unfold raggedFrom at none
      split at none
      · rename_i counted
        intro row member
        rcases List.mem_cons.mp member with rfl | later
        · exact counted
        · exact induction none row later
      · cases none

public theorem raggedFrom_some {count start position : Nat} {rows : List (List Carrier)}
    (found : raggedFrom count start rows = some position) :
    start ≤ position ∧ position - start < rows.length ∧
      (rows.getD (position - start) []).length ≠ count := by
  induction rows generalizing start with
  | nil => cases found
  | cons first rest induction =>
      unfold raggedFrom at found
      split at found
      · obtain ⟨after, below, wrong⟩ := induction found
        refine ⟨by omega, by simp; omega, ?_⟩
        rw [show position - start = (position - (start + 1)) + 1 by omega]
        simpa using wrong
      · rename_i wrong
        cases found
        exact ⟨Nat.le_refl _, by simp, by simpa using wrong⟩

/-- The first ragged row, or the row count when only the mean's length is
wrong. -/
@[expose] public def shapeFailure (mean : List Carrier) (covariance : List (List Carrier)) :
    Option Nat :=
  match raggedFrom covariance.length 0 covariance with
  | some row => some row
  | none => if mean.length = covariance.length then none else some covariance.length

public theorem shapeFailure_none {mean : List Carrier} {covariance : List (List Carrier)}
    (none : shapeFailure mean covariance = Option.none) :
    Square covariance ∧ mean.length = covariance.length := by
  unfold shapeFailure at none
  split at none
  · cases none
  · rename_i rows
    split at none
    · exact ⟨raggedFrom_none rows, by assumption⟩
    · cases none

/-! ### The symmetry pass -/

/-- The first column `j < count` where row `i` disagrees with column `i`. -/
@[expose] public def asymmetricColumn (matrix : List (List Carrier)) (row : Nat) : Nat → Option Nat
  | 0 => none
  | column + 1 =>
      match asymmetricColumn matrix row column with
      | some found => some found
      | none =>
          haveI := Classical.propDecidable (matrixEntry matrix row column = matrixEntry matrix column row)
          if matrixEntry matrix row column = matrixEntry matrix column row then none else some column

/-- The first pair `(i, j)` with `j < i < count`, in row order, where `Σᵢⱼ ≠ Σⱼᵢ`. -/
@[expose] public def asymmetricRow (matrix : List (List Carrier)) : Nat → Option (Nat × Nat)
  | 0 => none
  | row + 1 =>
      match asymmetricRow matrix row with
      | some found => some found
      | none => (asymmetricColumn matrix row row).map (fun column => (row, column))

public theorem asymmetricColumn_none {matrix : List (List Carrier)} {row : Nat} :
    ∀ {count : Nat}, asymmetricColumn matrix row count = none →
      ∀ column, column < count → matrixEntry matrix row column = matrixEntry matrix column row
  | 0, _, column, below => absurd below (Nat.not_lt_zero _)
  | count + 1, vanished, column, below => by
      unfold asymmetricColumn at vanished
      split at vanished
      · cases vanished
      · rename_i earlier
        split at vanished
        · rename_i equal
          rcases Nat.lt_or_ge column count with inside | outside
          · exact asymmetricColumn_none earlier column inside
          · rwa [show column = count by omega]
        · cases vanished

public theorem asymmetricColumn_some {matrix : List (List Carrier)} {row : Nat} :
    ∀ {count column : Nat}, asymmetricColumn matrix row count = some column →
      column < count ∧ matrixEntry matrix row column ≠ matrixEntry matrix column row
  | 0, _, found => by cases found
  | count + 1, column, found => by
      unfold asymmetricColumn at found
      split at found
      · rename_i earlier
        cases found
        have := asymmetricColumn_some earlier
        exact ⟨by omega, this.2⟩
      · split at found
        · cases found
        · rename_i different
          cases found
          exact ⟨by omega, different⟩

public theorem asymmetricRow_none {matrix : List (List Carrier)} :
    ∀ {count : Nat}, asymmetricRow matrix count = none →
      ∀ row column, row < count → column < row →
        matrixEntry matrix row column = matrixEntry matrix column row
  | 0, _, row, _, below, _ => absurd below (Nat.not_lt_zero _)
  | count + 1, vanished, row, column, below, ordered => by
      unfold asymmetricRow at vanished
      split at vanished
      · cases vanished
      · rename_i earlier
        rcases Nat.lt_or_ge row count with inside | outside
        · exact asymmetricRow_none earlier row column inside ordered
        · have last : row = count := by omega
          subst last
          cases found : asymmetricColumn matrix row row with
          | none => exact asymmetricColumn_none found column ordered
          | some _ =>
              rw [found] at vanished
              cases vanished

public theorem asymmetricRow_some {matrix : List (List Carrier)} :
    ∀ {count row column : Nat}, asymmetricRow matrix count = some (row, column) →
      row < count ∧ column < row ∧ matrixEntry matrix row column ≠ matrixEntry matrix column row
  | 0, _, _, found => by cases found
  | count + 1, row, column, found => by
      unfold asymmetricRow at found
      split at found
      · rename_i earlier
        cases found
        have := asymmetricRow_some earlier
        exact ⟨by omega, this.2⟩
      · cases located : asymmetricColumn matrix count count with
        | none =>
            rw [located] at found
            cases found
        | some located_column =>
            rw [located] at found
            cases found
            have := asymmetricColumn_some located
            exact ⟨by omega, this⟩

/-- The first asymmetric pair of the leading square block. -/
@[expose] public def asymmetry (covariance : List (List Carrier)) : Option (Nat × Nat) :=
  asymmetricRow covariance covariance.length

public theorem asymmetry_none {covariance : List (List Carrier)}
    (none : asymmetry covariance = Option.none) : Symmetric covariance := by
  intro first second firstBelow secondBelow
  rcases Nat.lt_trichotomy first second with less | equal | greater
  · exact (asymmetricRow_none none second first secondBelow less).symm
  · rw [equal]
  · exact asymmetricRow_none none first second firstBelow greater

/-! ### The factor fold -/

/-- The regression's variances are positive at every mean once they are at
one. -/
public theorem positivePivots_iff (mean : List Carrier) (covariance : List (List Carrier)) :
    PositivePivots covariance ↔ ∀ row ∈ regress mean covariance, lt zero row.variance := by
  constructor
  · exact fun positive => regress_positive positive mean
  · intro positive row member
    have mapped : row.variance ∈ (regress mean covariance).map Row.variance := by
      rw [(regress_shape mean [] covariance).2]
      exact List.mem_map_of_mem member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp mapped
    rw [← same]
    exact positive original originalMember

public theorem positivePivots_concat {covariance : List (List Carrier)} {row : List Carrier}
    (mean : List Carrier) :
    PositivePivots (covariance ++ [row]) ↔
      PositivePivots covariance ∧ lt zero (regressRow mean (regress mean covariance) row).variance := by
  rw [positivePivots_iff mean, positivePivots_iff mean, regress_concat]
  constructor
  · intro positive
    exact ⟨fun current member => positive current (List.mem_append_left _ member),
      positive _ (by simp)⟩
  · rintro ⟨earlier, last⟩ current member
    rcases List.mem_append.mp member with inside | final
    · exact earlier current inside
    · rw [List.mem_singleton.mp final]
      exact last

/-- One row of the fold. The new row is regressed on the accepted prefix, and
it is accepted only when its pivot is positive. Otherwise the fold stops with
the row's index and its pivot. -/
@[expose] public def factorStep (mean : List Carrier) :
    Except (Nat × Carrier) (List Row) → List Carrier → Except (Nat × Carrier) (List Row)
  | .error failure, _ => .error failure
  | .ok rows, row =>
      haveI := Classical.propDecidable (lt zero (regressRow mean rows row).variance)
      if lt zero (regressRow mean rows row).variance then .ok (rows ++ [regressRow mean rows row])
      else .error (rows.length, (regressRow mean rows row).variance)

public theorem factorStep_positive {mean : List Carrier} {rows : List Row} {row : List Carrier}
    (positive : lt zero (regressRow mean rows row).variance) :
    factorStep mean (.ok rows) row = .ok (rows ++ [regressRow mean rows row]) := by
  simp only [factorStep]
  exact ite_eq_left positive

public theorem factorStep_nonpositive {mean : List Carrier} {rows : List Row} {row : List Carrier}
    (nonpositive : ¬lt zero (regressRow mean rows row).variance) :
    factorStep mean (.ok rows) row = .error (rows.length, (regressRow mean rows row).variance) := by
  simp only [factorStep]
  exact ite_eq_right nonpositive

/-- The left fold of `factorStep` over the covariance's rows. -/
@[expose] public def factorRows (mean : List Carrier) (covariance : List (List Carrier)) :
    Except (Nat × Carrier) (List Row) :=
  covariance.foldl (factorStep mean) (.ok [])

public theorem factorRows_concat (mean : List Carrier) (covariance : List (List Carrier))
    (row : List Carrier) :
    factorRows mean (covariance ++ [row]) = factorStep mean (factorRows mean covariance) row := by
  simp [factorRows, List.foldl_append]

/-- A covariance with positive pivots folds to its regression rows. -/
public theorem factorRows_of_positive {mean : List Carrier} {covariance : List (List Carrier)}
    (positive : PositivePivots covariance) :
    factorRows mean covariance = .ok (regress mean covariance) := by
  induction covariance using concat_induction with
  | nil => rfl
  | concat covariance row induction =>
      obtain ⟨earlier, last⟩ := (positivePivots_concat mean).mp positive
      rw [factorRows_concat, induction earlier, regress_concat, factorStep_positive last]

/-- A fold that succeeds accepted every pivot. -/
public theorem factorRows_ok {mean : List Carrier} {covariance : List (List Carrier)}
    {rows : List Row} (succeeded : factorRows mean covariance = .ok rows) :
    PositivePivots covariance := by
  induction covariance using concat_induction generalizing rows with
  | nil => intro row member; cases member
  | concat covariance row induction =>
      rw [factorRows_concat] at succeeded
      cases state : factorRows mean covariance with
      | error failure =>
          rw [state] at succeeded
          cases succeeded
      | ok earlier =>
          rw [state] at succeeded
          have positive := induction state
          rw [factorRows_of_positive positive, Except.ok.injEq] at state
          subst state
          by_cases last : lt zero (regressRow mean (regress mean covariance) row).variance
          · exact (positivePivots_concat mean).mpr ⟨positive, last⟩
          · rw [factorStep_nonpositive last] at succeeded
            cases succeeded

/-- A fold that fails stops at the first nonpositive pivot: the prefix before
row `k` has positive pivots, and `v` is row `k`'s Schur complement. -/
public theorem factorRows_error {mean : List Carrier} {covariance : List (List Carrier)}
    {position : Nat} {value : Carrier}
    (failed : factorRows mean covariance = .error (position, value)) :
    ∃ front row back, covariance = front ++ row :: back ∧ front.length = position ∧
      PositivePivots front ∧ value = (regressRow mean (regress mean front) row).variance ∧
        ¬lt zero value := by
  induction covariance using concat_induction with
  | nil => cases failed
  | concat covariance last induction =>
      rw [factorRows_concat] at failed
      cases state : factorRows mean covariance with
      | error failure =>
          rw [state] at failed
          cases failed
          obtain ⟨front, row, back, split, counted, positive, pivot, nonpositive⟩ := induction state
          exact ⟨front, row, back ++ [last], by rw [split]; simp, counted, positive, pivot,
            nonpositive⟩
      | ok earlier =>
          have positive := factorRows_ok state
          rw [factorRows_of_positive positive] at failed
          by_cases accepted : lt zero (regressRow mean (regress mean covariance) last).variance
          · rw [factorStep_positive accepted] at failed
            cases failed
          · rw [factorStep_nonpositive accepted] at failed
            cases failed
            exact ⟨covariance, last, [], rfl, (regress_length _ _).symm, positive, rfl, accepted⟩

/-! ### The pivot as a quadratic form -/

public theorem sumBelow_zero (count : Nat) : sumBelow count (fun _ => zero) = zero := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change add (sumBelow count _) zero = zero
      rw [induction, add_zero]

public theorem sumBelow_neg (count : Nat) (term : Nat → Carrier) :
    sumBelow count (fun index => neg (term index)) = neg (sumBelow count term) := by
  induction count with
  | zero => exact neg_zero.symm
  | succ count induction =>
      change add (sumBelow count _) _ = neg (add (sumBelow count term) _)
      rw [induction]
      real_grind

/-- Coefficients that vanish from `count` on read only the leading block. -/
public theorem quadratic_vanish {count total : Nat} {coefficient : Nat → Carrier}
    (vanish : ∀ index, count ≤ index → coefficient index = zero) (le : count ≤ total)
    (matrix : Nat → Nat → Carrier) :
    quadratic total coefficient matrix = quadratic count coefficient matrix := by
  induction total with
  | zero =>
      rw [Nat.le_zero.mp le]
  | succ total induction =>
      rcases Nat.lt_or_ge total count with inside | outside
      · rw [show count = total + 1 by omega]
      · rw [quadratic_succ, induction outside, vanish total outside]
        have left : sumBelow total (fun first => mul (mul (coefficient first) zero)
            (matrix first total)) = zero := by
          rw [sumBelow_congr fun first _ => by rw [mul_zero, zero_mul], sumBelow_zero]
        have right : sumBelow total (fun second => mul (mul zero (coefficient second))
            (matrix total second)) = zero := by
          rw [sumBelow_congr fun second _ => by rw [zero_mul, zero_mul], sumBelow_zero]
        rw [left, right]
        real_grind

/-- The coefficients `(−b, 1, 0, …)` of row `k`'s regression residual. -/
@[expose] public def residualCoefficients (coefficients : List Carrier) (index : Nat) : Carrier :=
  if index < coefficients.length then neg (entry coefficients index)
  else if index = coefficients.length then one else zero

/-- Row `k`'s pivot is the quadratic form of `Σ` at the residual coefficients
`(−b, 1, 0, …)`, so a nonpositive pivot witnesses that `Σ` is not positive
definite. It needs the leading block before row `k` to have positive pivots and
the covariance to be symmetric. -/
public theorem pivot_quadratic {mean : List Carrier} {front back : List (List Carrier)}
    {row : List Carrier} (positive : PositivePivots front)
    (symmetric : Symmetric (front ++ row :: back)) :
    quadratic (front ++ row :: back).length
        (residualCoefficients (regressRow mean (regress mean front) row).coefficients)
        (matrixEntry (front ++ row :: back)) =
      (regressRow mean (regress mean front) row).variance := by
  let earlier := ofMoments mean front positive
  let count := front.length
  have earlierLength : earlier.length = count := ofMoments_length _ _ _
  have triangular := regress_triangular mean front
  have solvedLength : (solve (regress mean front) row).length = count := by
    rw [solve_length triangular, regress_length]
  have prefixSymmetric : Symmetric front := by
    intro first second firstBelow secondBelow
    have value := symmetric first second (by simp; omega) (by simp; omega)
    rwa [getD_append_left _ firstBelow, getD_append_left _ secondBelow] at value
  have readFront : ∀ first second, first < count →
      matrixEntry (front ++ row :: back) first second = entry (front.getD first []) second :=
    fun first second below => by unfold matrixEntry; rw [getD_append_left _ below]
  have readRow : ∀ second, matrixEntry (front ++ row :: back) count second = entry row second :=
    fun second => by
      unfold matrixEntry
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
  -- The solved coefficients satisfy `C b = σ` on the prefix.
  have solved : ∀ index, index < count →
      sumBelow count (fun other => mul (entry (front.getD index []) other)
        (entry (solve (regress mean front) row) other)) = entry row index := by
    intro index below
    have value := earlier.act_solve row (index := index) (by rw [earlierLength]; exact below)
    unfold Network.act at value
    rw [earlierLength] at value
    rw [← value]
    exact sumBelow_congr fun other otherBelow => by
      rw [ofMoments_covarianceAt positive prefixSymmetric below otherBelow]
      rfl
  have total : count + 1 ≤ (front ++ row :: back).length := by
    show front.length + 1 ≤ _
    simp
  change quadratic _ (residualCoefficients (solve (regress mean front) row)) _ = sub _ _
  rw [quadratic_vanish (count := count + 1) (fun index above => by
      unfold residualCoefficients
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]) total,
    quadratic_succ]
  have atLast : residualCoefficients (solve (regress mean front) row) count = one := by
    unfold residualCoefficients
    rw [ite_eq_right (by omega), ite_eq_left solvedLength.symm]
  have below : ∀ index, index < count → residualCoefficients (solve (regress mean front) row) index =
      neg (entry (solve (regress mean front) row) index) := fun index inside => by
    unfold residualCoefficients
    rw [ite_eq_left (by omega)]
  rw [atLast]
  generalize bDefinition : solve (regress mean front) row = coefficients at solved solvedLength below
  -- The leading block: `bᵀ C b = bᵀ σ`.
  have block : quadratic count (residualCoefficients coefficients) (matrixEntry (front ++ row :: back)) =
      sumBelow count (fun index => mul (entry coefficients index) (entry row index)) := by
    unfold quadratic
    rw [sumBelow_congr fun first firstBelow => sumBelow_congr fun second secondBelow => by
      rw [below first firstBelow, below second secondBelow, readFront first second firstBelow]]
    apply sumBelow_congr
    intro first firstBelow
    rw [← solved first firstBelow, ← sumBelow_mul_left]
    apply sumBelow_congr
    intro second secondBelow
    real_grind
  have mirrored : ∀ index, index < count →
      matrixEntry (front ++ row :: back) index count = entry row index := fun index inside => by
    have value := symmetric index count (by simp; omega) (by show front.length < _; simp)
    change matrixEntry _ index count = matrixEntry _ count index at value
    rw [value, readRow]
  have column : sumBelow count (fun first => mul (mul (residualCoefficients coefficients first) one)
      (matrixEntry (front ++ row :: back) first count)) =
      neg (sumBelow count (fun index => mul (entry coefficients index) (entry row index))) := by
    rw [← sumBelow_neg]
    apply sumBelow_congr
    intro first firstBelow
    rw [below first firstBelow, mirrored first firstBelow]
    real_grind
  have across : sumBelow count (fun second => mul (mul one (residualCoefficients coefficients second))
      (matrixEntry (front ++ row :: back) count second)) =
      neg (sumBelow count (fun index => mul (entry coefficients index) (entry row index))) := by
    rw [← sumBelow_neg]
    apply sumBelow_congr
    intro second secondBelow
    rw [below second secondBelow, readRow]
    real_grind
  rw [block, column, across, readRow, regress_length, dot_eq_sumBelow, solvedLength]
  real_grind

/-- A pivot that the fold rejects is a nonpositive quadratic form at
coefficients that are one at its row, so the covariance is not positive
definite. -/
public theorem not_positiveDefinite_of_pivot {mean : List Carrier} {front back : List (List Carrier)}
    {row : List Carrier} (positive : PositivePivots front)
    (symmetric : Symmetric (front ++ row :: back))
    (nonpositive : ¬lt zero (regressRow mean (regress mean front) row).variance) :
    ¬PositiveDefinite (front ++ row :: back) := by
  intro definite
  apply nonpositive
  rw [← pivot_quadratic positive symmetric]
  apply definite
  refine ⟨front.length, by simp, ?_⟩
  have solvedLength : (regressRow mean (regress mean front) row).coefficients.length =
      front.length := by
    change (solve _ row).length = _
    rw [solve_length (regress_triangular mean front), regress_length]
  unfold residualCoefficients
  rw [ite_eq_right (by omega), ite_eq_left solvedLength.symm]
  exact one_ne_zero

/-! ### The typed result -/

/-- What `factor m Σ` found. -/
public inductive FieldResult where
  /-- Row `k < n` does not have `n` entries, or `k = n` and the mean does not. -/
  | shape (row : Nat)
  /-- `Σᵢⱼ ≠ Σⱼᵢ` with `j < i`: the matrix is not a covariance. -/
  | asymmetric (row column : Nat)
  /-- The first nonpositive Schur complement, at row `k`: the matrix is not
  positive definite, so the positive-definite route is unavailable. -/
  | pivot (row : Nat) (value : Carrier)
  /-- Native execution only: a pivot that is nonpositive, NaN or infinite in
  floating point. It certifies nothing about the exact matrix, and a consumer
  reads it as no answer. -/
  | numerical (row : Nat)
  /-- Success: the network whose mean and covariance are `m` and `Σ`. -/
  | network (network : Network)

/-- Factor a runtime mean and covariance: the shape pass, then the symmetry
pass, then the left fold of `factorStep` over the rows. -/
@[expose] public def factor (mean : List Carrier) (covariance : List (List Carrier)) :
    FieldResult :=
  match shapeFailure mean covariance with
  | some row => .shape row
  | none =>
      match asymmetry covariance with
      | some (row, column) => .asymmetric row column
      | none =>
          match folded : factorRows mean covariance with
          | .error (row, value) => .pivot row value
          | .ok _ => .network (ofMoments mean covariance (factorRows_ok folded))

/-- The exact factorization never answers `numerical`. -/
public theorem factor_ne_numerical (mean : List Carrier) (covariance : List (List Carrier))
    (row : Nat) : factor mean covariance ≠ .numerical row := by
  unfold factor
  split
  · intro equal; cases equal
  · split
    · intro equal; cases equal
    · split <;> intro equal <;> cases equal

/-- The passes a factorization that reaches the fold has passed. -/
public theorem factor_passes {mean : List Carrier} {covariance : List (List Carrier)}
    (reached : shapeFailure mean covariance = none ∧ asymmetry covariance = none) :
    Square covariance ∧ Symmetric covariance ∧ mean.length = covariance.length :=
  ⟨(shapeFailure_none reached.1).1, asymmetry_none reached.2, (shapeFailure_none reached.1).2⟩

/-- `factor_sound`: on `network N`, the matrix is a square symmetric
covariance and `N`'s mean and covariance recurrences are `m` and `Σ`. -/
public theorem factor_sound {mean : List Carrier} {covariance : List (List Carrier)}
    {network : Network} (answered : factor mean covariance = .network network) :
    Square covariance ∧ Symmetric covariance ∧ mean.length = covariance.length ∧
      network.mean = mean ∧ network.covariance = covariance := by
  unfold factor at answered
  split at answered
  · cases answered
  · rename_i shaped
    split at answered
    · cases answered
    · rename_i symmetric
      split at answered
      · cases answered
      · rename_i folded
        cases answered
        obtain ⟨square, symmetric, meanLength⟩ := factor_passes ⟨shaped, symmetric⟩
        exact ⟨square, symmetric, meanLength,
          ofMoments_mean (factorRows_ok folded) symmetric meanLength,
          ofMoments_covariance (factorRows_ok folded) symmetric square⟩

/-- `factor_pivot`: `pivot k v` means that `v ≤ 0` is the Schur complement at
row `k`, and it is the quadratic form of `Σ` at coefficients that are one at `k`
and zero past it. The rows before `k` have positive pivots. -/
public theorem factor_pivot {mean : List Carrier} {covariance : List (List Carrier)}
    {row : Nat} {value : Carrier} (answered : factor mean covariance = .pivot row value) :
    row < covariance.length ∧ ¬lt zero value ∧ PositivePivots (covariance.take row) ∧
      ∃ coefficient : Nat → Carrier, coefficient row = one ∧
        (∀ index, row < index → coefficient index = zero) ∧
        quadratic covariance.length coefficient (matrixEntry covariance) = value := by
  unfold factor at answered
  split at answered
  · cases answered
  · rename_i shaped
    split at answered
    · cases answered
    · rename_i asymmetric
      split at answered
      · rename_i folded
        cases answered
        obtain ⟨_, symmetric, _⟩ := factor_passes ⟨shaped, asymmetric⟩
        obtain ⟨front, current, back, split, counted, positive, pivot, nonpositive⟩ :=
          factorRows_error folded
        subst split
        subst counted
        have solvedLength : (regressRow mean (regress mean front) current).coefficients.length =
            front.length := by
          change (solve _ current).length = _
          rw [solve_length (regress_triangular mean front), regress_length]
        refine ⟨by simp, nonpositive, by simpa using positive, residualCoefficients
          (regressRow mean (regress mean front) current).coefficients, ?_, ?_, ?_⟩
        · unfold residualCoefficients
          rw [ite_eq_right (by omega), ite_eq_left solvedLength.symm]
        · intro index above
          unfold residualCoefficients
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        · rw [pivot]
          exact pivot_quadratic positive symmetric
      · cases answered

public theorem factor_pivot_not_positiveDefinite {mean : List Carrier}
    {covariance : List (List Carrier)} {row : Nat} {value : Carrier}
    (answered : factor mean covariance = .pivot row value) : ¬PositiveDefinite covariance := by
  obtain ⟨_, nonpositive, _, coefficient, atRow, _, quadratic⟩ := factor_pivot answered
  intro definite
  apply nonpositive
  rw [← quadratic]
  exact definite coefficient ⟨row, (factor_pivot answered).1, by rw [atRow]; exact one_ne_zero⟩

/-- `factor_complete`: in exact arithmetic every square, symmetric,
positive-definite covariance with a mean of its length answers `network`. -/
public theorem factor_complete {mean : List Carrier} {covariance : List (List Carrier)}
    (square : Square covariance) (symmetric : Symmetric covariance)
    (meanLength : mean.length = covariance.length) (definite : PositiveDefinite covariance) :
    ∃ network, factor mean covariance = .network network := by
  have shaped : shapeFailure mean covariance = none := by
    unfold shapeFailure
    have ragged : raggedFrom covariance.length 0 covariance = none := by
      suffices general : ∀ (start : Nat) (rows : List (List Carrier)),
          (∀ row ∈ rows, row.length = covariance.length) →
            raggedFrom covariance.length start rows = none from
        general 0 covariance square
      intro start rows counted
      induction rows generalizing start with
      | nil => rfl
      | cons first rest induction =>
          unfold raggedFrom
          rw [ite_eq_left (counted first (by simp))]
          exact induction (start + 1) fun row member => counted row (by simp [member])
    rw [ragged]
    exact ite_eq_left meanLength
  have symmetricPass : asymmetry covariance = none := by
    cases found : asymmetry covariance with
    | none => rfl
    | some pair =>
        obtain ⟨row, column⟩ := pair
        obtain ⟨below, ordered, different⟩ := asymmetricRow_some found
        exact absurd (symmetric row column below (by omega)) different
  cases folded : factorRows mean covariance with
  | error failure =>
      obtain ⟨row, value⟩ := failure
      obtain ⟨front, current, back, split, _, positive, pivot, nonpositive⟩ :=
        factorRows_error folded
      subst split
      rw [pivot] at nonpositive
      exact absurd definite (not_positiveDefinite_of_pivot positive symmetric nonpositive)
  | ok rows =>
      refine ⟨ofMoments mean covariance (factorRows_ok folded), ?_⟩
      unfold factor
      rw [shaped]
      simp only
      rw [symmetricPass]
      simp only
      split
      · rename_i failed
        rw [folded] at failed
        cases failed
      · rfl

/-- `shape k` names a row without one entry per row, or the mean's length. -/
public theorem factor_shape {mean : List Carrier} {covariance : List (List Carrier)}
    {row : Nat} (answered : factor mean covariance = .shape row) :
    (row < covariance.length ∧ (covariance.getD row []).length ≠ covariance.length) ∨
      (row = covariance.length ∧ mean.length ≠ covariance.length) := by
  unfold factor at answered
  split at answered
  · rename_i found
    cases answered
    unfold shapeFailure at found
    split at found
    · rename_i ragged
      cases found
      obtain ⟨_, below, wrong⟩ := raggedFrom_some ragged
      exact Or.inl ⟨by simpa using below, by simpa using wrong⟩
    · split at found
      · cases found
      · rename_i wrong
        cases found
        exact Or.inr ⟨rfl, wrong⟩
  · split at answered
    · cases answered
    · split at answered <;> cases answered

/-- `asymmetric i j` names `j < i < n` with `Σᵢⱼ ≠ Σⱼᵢ`. -/
public theorem factor_asymmetric {mean : List Carrier} {covariance : List (List Carrier)}
    {row column : Nat} (answered : factor mean covariance = .asymmetric row column) :
    row < covariance.length ∧ column < row ∧
      matrixEntry covariance row column ≠ matrixEntry covariance column row := by
  unfold factor at answered
  split at answered
  · cases answered
  · split at answered
    · rename_i found
      cases answered
      exact asymmetricRow_some found
    · split at answered <;> cases answered

end
end Problib.Analysis.Gaussian
