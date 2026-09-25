module

public import Problib.Analysis.Real.MultiIndex

/-! Multivariate signed power series, grouped into finite degree shells.

The constant coefficient is evaluated separately. Every other shell has
positive total degree, and its finite sum is an ordinary signed real. This
grouping allows the convergence certificate to use the signed-series floor
without an implicit sum over a function type.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

/-- The finite sum of one homogeneous degree. -/
@[expose] public def shellTerm {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    selection.Carrier :=
  (MultiIndex.degreeShell dimension degreeValue).foldr
    (fun index total =>
      add (mul (coefficients index)
        (MultiIndex.monomial dimension index displacement)) total)
    zero

/-- The sum of the magnitudes of every monomial in a degree shell. -/
@[expose] public def shellMagnitude {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    selection.Carrier :=
  (MultiIndex.degreeShell dimension degreeValue).foldr
    (fun index total =>
      add (abs (mul (coefficients index)
        (MultiIndex.monomial dimension index displacement))) total)
    zero

public theorem shellTerm_zero_degree {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) :
    shellTerm coefficients displacement 0 =
      coefficients (MultiIndex.zeroIndex dimension) := by
  unfold shellTerm
  rw [MultiIndex.degreeShell_zero_singleton]
  simp only [List.foldr_cons, List.foldr_nil,
    MultiIndex.monomial_zeroIndex, mul_one, add_zero]

public theorem shellMagnitude_zero_degree {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) :
    shellMagnitude coefficients displacement 0 =
      abs (coefficients (MultiIndex.zeroIndex dimension)) := by
  unfold shellMagnitude
  rw [MultiIndex.degreeShell_zero_singleton]
  simp only [List.foldr_cons, List.foldr_nil,
    MultiIndex.monomial_zeroIndex, mul_one, add_zero]

public theorem shellTerm_congr_on {dimension degreeValue : Nat}
    {first second : MultiIndex.carrier dimension → selection.Carrier}
    (displacement : FiniteVector.carrier dimension)
    (equal : ∀ index,
      index ∈ MultiIndex.degreeShell dimension degreeValue →
        first index = second index) :
    shellTerm first displacement degreeValue =
      shellTerm second displacement degreeValue := by
  unfold shellTerm
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices → first index = second index) →
      indices.foldr
        (fun index total => add (mul (first index)
          (MultiIndex.monomial dimension index displacement)) total) zero =
      indices.foldr
        (fun index total => add (mul (second index)
          (MultiIndex.monomial dimension index displacement)) total) zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro matched
        simp only [List.foldr_cons, matched index (List.mem_cons_self)]
        exact congrArg (add (mul (second index)
          (MultiIndex.monomial dimension index displacement)))
          (induction (fun later member =>
            matched later (List.mem_cons_of_mem index member)))
  exact go (MultiIndex.degreeShell dimension degreeValue) equal

public theorem shellMagnitude_congr_on {dimension degreeValue : Nat}
    {first second : MultiIndex.carrier dimension → selection.Carrier}
    (displacement : FiniteVector.carrier dimension)
    (equal : ∀ index,
      index ∈ MultiIndex.degreeShell dimension degreeValue →
        first index = second index) :
    shellMagnitude first displacement degreeValue =
      shellMagnitude second displacement degreeValue := by
  unfold shellMagnitude
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices → first index = second index) →
      indices.foldr
        (fun index total => add (abs (mul (first index)
          (MultiIndex.monomial dimension index displacement))) total) zero =
      indices.foldr
        (fun index total => add (abs (mul (second index)
          (MultiIndex.monomial dimension index displacement))) total) zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro matched
        simp only [List.foldr_cons, matched index (List.mem_cons_self)]
        exact congrArg (add (abs (mul (second index)
          (MultiIndex.monomial dimension index displacement))))
          (induction (fun later member =>
            matched later (List.mem_cons_of_mem index member)))
  exact go (MultiIndex.degreeShell dimension degreeValue) equal

/-- A finite shell has no hidden cancellation in its magnitude bound. -/
public theorem abs_shellTerm_le_magnitude {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    le (abs (shellTerm coefficients displacement degreeValue))
      (shellMagnitude coefficients displacement degreeValue) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      le
        (abs (indices.foldr
          (fun index total => add (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement)) total) zero))
        (indices.foldr
          (fun index total => add (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement))) total) zero) := by
    intro indices
    induction indices with
    | nil =>
        simp only [List.foldr_nil]
        rw [abs_zero]
        exact le_refl zero
    | cons index rest induction =>
        simp only [List.foldr_cons]
        exact le_trans (abs_add_le _ _)
          (add_le_add (le_refl _) induction)
  exact go (MultiIndex.degreeShell dimension degreeValue)

public theorem shellMagnitude_nonnegative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    le zero (shellMagnitude coefficients displacement degreeValue) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      le zero
        (indices.foldr
          (fun index total => add (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement))) total)
          zero) := by
    intro indices
    induction indices with
    | nil => exact le_refl zero
    | cons index rest induction =>
        simp only [List.foldr_cons]
        exact add_nonnegative (abs_nonnegative _) induction
  exact go (MultiIndex.degreeShell dimension degreeValue)

private theorem abs_partial_sum_le (values : Nat → selection.Carrier)
    (count : Nat) :
    le (abs (partialSum values count))
      (partialSum (fun index => abs (values index)) count) := by
  induction count with
  | zero =>
      rw [partial_sum_zero, partial_sum_zero, abs_zero]
      exact le_refl zero
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ]
      exact le_trans (abs_add_le _ _)
        (add_le_add induction (le_refl _))

/-- A nonnegative constant-radius vector dominates the coefficientwise
magnitude of a shell at every vector inside its closed coordinate box. -/
public theorem shellMagnitude_le_constant {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (displacement coordinate)) radius)
    (degreeValue : Nat) :
    le (shellMagnitude coefficients displacement degreeValue)
      (shellMagnitude coefficients (fun _ => radius) degreeValue) := by
  have termBound (index : MultiIndex.carrier dimension) :
      le (abs (mul (coefficients index)
          (MultiIndex.monomial dimension index displacement)))
        (abs (mul (coefficients index)
          (MultiIndex.monomial dimension index (fun _ => radius)))) := by
    rw [abs_mul, abs_mul,
      MultiIndex.monomial_constant_radius,
      abs_of_nonnegative (power_nonnegative nonnegative _)]
    exact mul_le_mul_nonnegative_left
      (MultiIndex.abs_monomial_le_power dimension index displacement
        nonnegative coordinates)
      (abs_nonnegative (coefficients index))
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      le
        (indices.foldr
          (fun index total => add (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement))) total) zero)
        (indices.foldr
          (fun index total => add (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index (fun _ => radius)))) total)
          zero) := by
    intro indices
    induction indices with
    | nil => exact le_refl zero
    | cons index rest induction =>
        simp only [List.foldr_cons]
        exact add_le_add (termBound index) induction
  exact go (MultiIndex.degreeShell dimension degreeValue)

/-- Finite shell summation distributes over coefficient addition. -/
public theorem shellTerm_add {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    shellTerm (fun index => add (first index) (second index))
      displacement degreeValue =
    add (shellTerm first displacement degreeValue)
      (shellTerm second displacement degreeValue) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      indices.foldr
        (fun index total => add (mul (add (first index) (second index))
          (MultiIndex.monomial dimension index displacement)) total) zero =
      add
        (indices.foldr
          (fun index total => add (mul (first index)
            (MultiIndex.monomial dimension index displacement)) total) zero)
        (indices.foldr
          (fun index total => add (mul (second index)
            (MultiIndex.monomial dimension index displacement)) total) zero) := by
    intro indices
    induction indices with
    | nil => simp only [List.foldr_nil, zero_add]
    | cons index rest induction =>
        simp only [List.foldr_cons]
        rw [add_mul, induction]
        ac_rfl
  exact go (MultiIndex.degreeShell dimension degreeValue)

public theorem shellTerm_scale {dimension : Nat}
    (factor : selection.Carrier)
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    shellTerm (fun index => mul factor (coefficients index))
      displacement degreeValue =
    mul factor (shellTerm coefficients displacement degreeValue) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      indices.foldr
        (fun index total => add
          (mul (mul factor (coefficients index))
            (MultiIndex.monomial dimension index displacement)) total) zero =
      mul factor
        (indices.foldr
          (fun index total => add (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement)) total) zero) := by
    intro indices
    induction indices with
    | nil => simp only [List.foldr_nil, mul_zero]
    | cons index rest induction =>
        simp only [List.foldr_cons, mul_add]
        rw [← mul_assoc, induction]
  exact go (MultiIndex.degreeShell dimension degreeValue)

public theorem shellMagnitude_scale {dimension : Nat}
    (factor : selection.Carrier)
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    shellMagnitude (fun index => mul factor (coefficients index))
      displacement degreeValue =
    mul (abs factor) (shellMagnitude coefficients displacement degreeValue) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      indices.foldr
        (fun index total => add
          (abs (mul (mul factor (coefficients index))
            (MultiIndex.monomial dimension index displacement))) total) zero =
      mul (abs factor)
        (indices.foldr
          (fun index total => add (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index displacement))) total)
          zero) := by
    intro indices
    induction indices with
    | nil => simp only [List.foldr_nil, mul_zero]
    | cons index rest induction =>
        simp only [List.foldr_cons, mul_add]
        rw [mul_assoc factor (coefficients index)
          (MultiIndex.monomial dimension index displacement),
          abs_mul, induction]
  exact go (MultiIndex.degreeShell dimension degreeValue)

public theorem shellMagnitude_add_le {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    le (shellMagnitude (fun index => add (first index) (second index))
        displacement degreeValue)
      (add (shellMagnitude first displacement degreeValue)
        (shellMagnitude second displacement degreeValue)) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      le
        (indices.foldr
          (fun index total => add (abs (mul (add (first index) (second index))
            (MultiIndex.monomial dimension index displacement))) total) zero)
        (add
          (indices.foldr
            (fun index total => add (abs (mul (first index)
              (MultiIndex.monomial dimension index displacement))) total) zero)
          (indices.foldr
            (fun index total => add (abs (mul (second index)
              (MultiIndex.monomial dimension index displacement))) total) zero)) := by
    intro indices
    induction indices with
    | nil => simp only [List.foldr_nil, zero_add, le_refl]
    | cons index rest induction =>
        simp only [List.foldr_cons]
        have triangle : le
            (abs (mul (add (first index) (second index))
              (MultiIndex.monomial dimension index displacement)))
            (add
              (abs (mul (first index)
                (MultiIndex.monomial dimension index displacement)))
              (abs (mul (second index)
                (MultiIndex.monomial dimension index displacement)))) := by
          rw [add_mul]
          exact abs_add_le _ _
        exact le_trans (add_le_add triangle induction) (by
          let firstHead := abs (mul (first index)
            (MultiIndex.monomial dimension index displacement))
          let secondHead := abs (mul (second index)
            (MultiIndex.monomial dimension index displacement))
          let firstTail := rest.foldr
            (fun index total => add (abs (mul (first index)
              (MultiIndex.monomial dimension index displacement))) total) zero
          let secondTail := rest.foldr
            (fun index total => add (abs (mul (second index)
              (MultiIndex.monomial dimension index displacement))) total) zero
          change le (add (add firstHead secondHead)
            (add firstTail secondTail))
            (add (add firstHead firstTail) (add secondHead secondTail))
          have rearranged :
              add (add firstHead secondHead) (add firstTail secondTail) =
                add (add firstHead firstTail) (add secondHead secondTail) := by
            ac_rfl
          rw [rearranged]
          exact le_refl _)
  exact go (MultiIndex.degreeShell dimension degreeValue)

/-- Positive-degree terms; the zero-degree coefficient is kept separate. -/
@[expose] public def tailTerms {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) : Nat → selection.Carrier :=
  fun degreeValue => shellTerm coefficients displacement (degreeValue + 1)

@[expose] public def tailMagnitudes {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) : Nat → selection.Carrier :=
  fun degreeValue => shellMagnitude coefficients displacement (degreeValue + 1)

public theorem tailMagnitudes_add_le {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    le (tailMagnitudes
        (fun index => add (first index) (second index))
        displacement degreeValue)
      (add (tailMagnitudes first displacement degreeValue)
        (tailMagnitudes second displacement degreeValue)) :=
  shellMagnitude_add_le first second displacement (degreeValue + 1)

public theorem tailMagnitudes_scale {dimension : Nat}
    (factor : selection.Carrier)
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    tailMagnitudes (fun index => mul factor (coefficients index))
      displacement degreeValue =
    mul (abs factor)
      (tailMagnitudes coefficients displacement degreeValue) :=
  shellMagnitude_scale factor coefficients displacement (degreeValue + 1)

public theorem tailMagnitudes_le_constant {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (displacement coordinate)) radius)
    (degreeValue : Nat) :
    le (tailMagnitudes coefficients displacement degreeValue)
      (tailMagnitudes coefficients (fun _ => radius) degreeValue) :=
  shellMagnitude_le_constant coefficients displacement nonnegative
    coordinates (degreeValue + 1)

public theorem tailTerms_add {dimension : Nat}
    (first second : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    tailTerms (fun index => add (first index) (second index))
      displacement degreeValue =
    add (tailTerms first displacement degreeValue)
      (tailTerms second displacement degreeValue) :=
  shellTerm_add first second displacement (degreeValue + 1)

public theorem tailTerms_scale {dimension : Nat}
    (factor : selection.Carrier)
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    tailTerms (fun index => mul factor (coefficients index))
      displacement degreeValue =
    mul factor (tailTerms coefficients displacement degreeValue) :=
  shellTerm_scale factor coefficients displacement (degreeValue + 1)

public theorem absolutely_summable_add {first second : Nat → selection.Carrier}
    (firstAbsolute : AbsolutelySummable first)
    (secondAbsolute : AbsolutelySummable second) :
    AbsolutelySummable (fun index => add (first index) (second index)) := by
  rcases firstAbsolute with ⟨firstUpper, firstBound⟩
  rcases secondAbsolute with ⟨secondUpper, secondBound⟩
  refine ⟨add firstUpper secondUpper, fun count => ?_⟩
  have triangle : ∀ index,
      le (abs (add (first index) (second index)))
        (add (abs (first index)) (abs (second index))) :=
    fun index => abs_add_le (first index) (second index)
  exact le_trans (partial_sum_le triangle count) (by
    rw [partial_sum_add]
    exact add_le_add (firstBound count) (secondBound count))

/-- Constant Taylor coefficients, zero in every positive degree. -/
@[expose] public def constantCoefficients (dimension : Nat)
    (constant : selection.Carrier) :
    MultiIndex.carrier dimension → selection.Carrier :=
  fun index => if MultiIndex.degree dimension index = 0 then constant else zero

/-- A finite sum with one supported index reads that index exactly once. -/
public theorem fold_single_support {α : Type} [DecidableEq α]
    (indices : List α) (nodup : indices.Nodup)
    (term : α → selection.Carrier) (selected : α)
    (weight : selection.Carrier)
    (on : term selected = weight)
    (off : ∀ index, index ≠ selected → term index = zero) :
    indices.foldr (fun index total => add (term index) total) zero =
      if selected ∈ indices then weight else zero := by
  induction indices with
  | nil => simp only [List.foldr_nil, List.not_mem_nil, ↓reduceIte]
  | cons head rest induction =>
      have restNodup := (List.nodup_cons.mp nodup).right
      by_cases headEqual : head = selected
      · subst head
        have absent : selected ∉ rest := (List.nodup_cons.mp nodup).left
        simp only [List.foldr_cons, on, induction restNodup,
          if_neg absent, add_zero]
        simp
      · have absent : selected ≠ head := fun equal => headEqual equal.symm
        simp only [List.foldr_cons, off head headEqual, zero_add,
          induction restNodup]
        simp [List.mem_cons, absent]

@[expose] public noncomputable def singleCoefficients {dimension : Nat}
    (selected : MultiIndex.carrier dimension)
    (coefficient : selection.Carrier) :
    MultiIndex.carrier dimension → selection.Carrier := by
  classical
  exact fun index => if selected = index then coefficient else zero

public theorem shellTerm_single {dimension degreeValue : Nat}
    (selected : MultiIndex.carrier dimension)
    (coefficient : selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeEqual : MultiIndex.degree dimension selected = degreeValue) :
    shellTerm (singleCoefficients selected coefficient)
      displacement degreeValue =
    mul coefficient (MultiIndex.monomial dimension selected displacement) := by
  classical
  have on :
      mul (singleCoefficients selected coefficient selected)
        (MultiIndex.monomial dimension selected displacement) =
      mul coefficient
        (MultiIndex.monomial dimension selected displacement) := by
    simp [singleCoefficients]
  have off : ∀ index, index ≠ selected →
      mul (singleCoefficients selected coefficient index)
        (MultiIndex.monomial dimension index displacement) = zero := by
    intro index distinct
    have reverse : selected ≠ index := fun equal => distinct equal.symm
    simp [singleCoefficients, reverse, zero_mul]
  have folded := fold_single_support
    (MultiIndex.degreeShell dimension degreeValue)
    (MultiIndex.degreeShell_nodup dimension degreeValue)
    (fun index => mul (singleCoefficients selected coefficient index)
      (MultiIndex.monomial dimension index displacement))
    selected
    (mul coefficient (MultiIndex.monomial dimension selected displacement))
    on off
  change shellTerm (singleCoefficients selected coefficient)
    displacement degreeValue =
    if selected ∈ MultiIndex.degreeShell dimension degreeValue then
      mul coefficient (MultiIndex.monomial dimension selected displacement)
    else zero at folded
  rw [folded, if_pos (MultiIndex.mem_degreeShell_iff.mpr degreeEqual)]

public theorem shellMagnitude_single {dimension degreeValue : Nat}
    (selected : MultiIndex.carrier dimension)
    (coefficient : selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (degreeEqual : MultiIndex.degree dimension selected = degreeValue) :
    shellMagnitude (singleCoefficients selected coefficient)
      displacement degreeValue =
    abs (mul coefficient
      (MultiIndex.monomial dimension selected displacement)) := by
  classical
  have on :
      abs (mul (singleCoefficients selected coefficient selected)
        (MultiIndex.monomial dimension selected displacement)) =
      abs (mul coefficient
        (MultiIndex.monomial dimension selected displacement)) := by
    simp [singleCoefficients]
  have off : ∀ index, index ≠ selected →
      abs (mul (singleCoefficients selected coefficient index)
        (MultiIndex.monomial dimension index displacement)) = zero := by
    intro index distinct
    have reverse : selected ≠ index := fun equal => distinct equal.symm
    simp [singleCoefficients, reverse, zero_mul, abs_zero]
  have folded := fold_single_support
    (MultiIndex.degreeShell dimension degreeValue)
    (MultiIndex.degreeShell_nodup dimension degreeValue)
    (fun index => abs (mul (singleCoefficients selected coefficient index)
      (MultiIndex.monomial dimension index displacement)))
    selected
    (abs (mul coefficient
      (MultiIndex.monomial dimension selected displacement)))
    on off
  change shellMagnitude (singleCoefficients selected coefficient)
    displacement degreeValue =
    if selected ∈ MultiIndex.degreeShell dimension degreeValue then
      abs (mul coefficient
        (MultiIndex.monomial dimension selected displacement))
    else zero at folded
  rw [folded, if_pos (MultiIndex.mem_degreeShell_iff.mpr degreeEqual)]

@[expose] public noncomputable def coordinateCoefficients {dimension : Nat}
    (selected : Fin dimension) :
    MultiIndex.carrier dimension → selection.Carrier := by
  classical
  exact fun index =>
    if index = MultiIndex.unitIndex selected then one else zero

public theorem coordinate_shellTerm {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    shellTerm (coordinateCoefficients selected) displacement degreeValue =
      if 1 = degreeValue then displacement selected else zero := by
  classical
  let unit := MultiIndex.unitIndex selected
  have on :
      mul (coordinateCoefficients selected unit)
        (MultiIndex.monomial dimension unit displacement) =
      MultiIndex.monomial dimension unit displacement := by
    change mul (if unit = MultiIndex.unitIndex selected then one else zero)
      (MultiIndex.monomial dimension unit displacement) = _
    rw [if_pos (show unit = MultiIndex.unitIndex selected by rfl), one_mul]
  have off : ∀ index, index ≠ unit →
      mul (coordinateCoefficients selected index)
        (MultiIndex.monomial dimension index displacement) = zero := by
    intro index distinct
    simp [coordinateCoefficients, unit, distinct, zero_mul]
  have folded := fold_single_support
    (MultiIndex.degreeShell dimension degreeValue)
    (MultiIndex.degreeShell_nodup dimension degreeValue)
    (fun index => mul (coordinateCoefficients selected index)
      (MultiIndex.monomial dimension index displacement))
    unit (MultiIndex.monomial dimension unit displacement) on off
  change shellTerm (coordinateCoefficients selected) displacement degreeValue =
    if unit ∈ MultiIndex.degreeShell dimension degreeValue then
      MultiIndex.monomial dimension unit displacement else zero at folded
  rw [folded]
  by_cases degreeOne : 1 = degreeValue
  · have member : unit ∈ MultiIndex.degreeShell dimension degreeValue :=
      MultiIndex.mem_degreeShell_iff.mpr (by
        rw [show MultiIndex.degree dimension unit = 1 from
          MultiIndex.degree_unitIndex dimension selected]
        exact degreeOne)
    rw [if_pos member, if_pos degreeOne]
    exact MultiIndex.monomial_unitIndex dimension selected displacement
  · have absent : unit ∉ MultiIndex.degreeShell dimension degreeValue := by
      intro member
      apply degreeOne
      rw [← MultiIndex.degree_unitIndex dimension selected]
      exact MultiIndex.degree_of_mem_shell member
    rw [if_neg absent, if_neg degreeOne]

public theorem coordinate_shellMagnitude {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension)
    (degreeValue : Nat) :
    shellMagnitude (coordinateCoefficients selected)
      displacement degreeValue =
      if 1 = degreeValue then abs (displacement selected) else zero := by
  classical
  let unit := MultiIndex.unitIndex selected
  have on :
      abs (mul (coordinateCoefficients selected unit)
        (MultiIndex.monomial dimension unit displacement)) =
      abs (MultiIndex.monomial dimension unit displacement) := by
    change abs (mul
      (if unit = MultiIndex.unitIndex selected then one else zero)
      (MultiIndex.monomial dimension unit displacement)) = _
    rw [if_pos (show unit = MultiIndex.unitIndex selected by rfl), one_mul]
  have off : ∀ index, index ≠ unit →
      abs (mul (coordinateCoefficients selected index)
        (MultiIndex.monomial dimension index displacement)) = zero := by
    intro index distinct
    simp [coordinateCoefficients, unit, distinct, zero_mul, abs_zero]
  have folded := fold_single_support
    (MultiIndex.degreeShell dimension degreeValue)
    (MultiIndex.degreeShell_nodup dimension degreeValue)
    (fun index => abs (mul (coordinateCoefficients selected index)
      (MultiIndex.monomial dimension index displacement)))
    unit (abs (MultiIndex.monomial dimension unit displacement)) on off
  change shellMagnitude (coordinateCoefficients selected)
    displacement degreeValue =
    if unit ∈ MultiIndex.degreeShell dimension degreeValue then
      abs (MultiIndex.monomial dimension unit displacement) else zero at folded
  rw [folded]
  by_cases degreeOne : 1 = degreeValue
  · have member : unit ∈ MultiIndex.degreeShell dimension degreeValue :=
      MultiIndex.mem_degreeShell_iff.mpr (by
        rw [show MultiIndex.degree dimension unit = 1 from
          MultiIndex.degree_unitIndex dimension selected]
        exact degreeOne)
    rw [if_pos member, if_pos degreeOne,
      MultiIndex.monomial_unitIndex]
  · have absent : unit ∉ MultiIndex.degreeShell dimension degreeValue := by
      intro member
      apply degreeOne
      rw [← MultiIndex.degree_unitIndex dimension selected]
      exact MultiIndex.degree_of_mem_shell member
    rw [if_neg absent, if_neg degreeOne]

public theorem coordinate_tail_zero {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension) :
    tailTerms (coordinateCoefficients selected) displacement 0 =
      displacement selected := by
  change shellTerm (coordinateCoefficients selected) displacement 1 = _
  rw [coordinate_shellTerm, if_pos rfl]

public theorem coordinate_tail_succ {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension) (index : Nat) :
    tailTerms (coordinateCoefficients selected) displacement (index + 1) =
      zero := by
  change shellTerm (coordinateCoefficients selected) displacement
    ((index + 1) + 1) = zero
  rw [coordinate_shellTerm, if_neg (by omega)]

public theorem coordinate_tail_magnitude_zero {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension) :
    tailMagnitudes (coordinateCoefficients selected) displacement 0 =
      abs (displacement selected) := by
  change shellMagnitude (coordinateCoefficients selected) displacement 1 = _
  rw [coordinate_shellMagnitude, if_pos rfl]

public theorem coordinate_tail_magnitude_succ {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension) (index : Nat) :
    tailMagnitudes (coordinateCoefficients selected) displacement
      (index + 1) = zero := by
  change shellMagnitude (coordinateCoefficients selected) displacement
    ((index + 1) + 1) = zero
  rw [coordinate_shellMagnitude, if_neg (by omega)]

public theorem shellTerm_zero_of_coefficients {dimension degreeValue : Nat}
    {coefficients : MultiIndex.carrier dimension → selection.Carrier}
    (displacement : FiniteVector.carrier dimension)
    (zeroOn : ∀ index,
      index ∈ MultiIndex.degreeShell dimension degreeValue →
        coefficients index = zero) :
    shellTerm coefficients displacement degreeValue = zero := by
  unfold shellTerm
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices → coefficients index = zero) →
      indices.foldr
        (fun index total => add (mul (coefficients index)
          (MultiIndex.monomial dimension index displacement)) total)
        zero = zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro vanished
        simp only [List.foldr_cons, vanished index (List.mem_cons_self),
          zero_mul, zero_add]
        apply induction
        intro later member
        exact vanished later (List.mem_cons_of_mem index member)
  exact go (MultiIndex.degreeShell dimension degreeValue) zeroOn

public theorem constant_tail_zero (dimension : Nat)
    (constant : selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    tailTerms (constantCoefficients dimension constant)
      displacement degreeValue = zero := by
  apply shellTerm_zero_of_coefficients
  intro index member
  have degreeEqual := MultiIndex.degree_of_mem_shell member
  simp only [constantCoefficients, degreeEqual]
  simp

private theorem partial_sum_zero_terms (count : Nat) :
    partialSum (fun _ : Nat => zero) count = zero := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partial_sum_succ, induction, add_zero]

public theorem constant_absolute (dimension : Nat)
    (constant : selection.Carrier)
    (displacement : FiniteVector.carrier dimension) :
    AbsolutelySummable
      (tailTerms (constantCoefficients dimension constant) displacement) := by
  refine ⟨zero, fun count => ?_⟩
  have equal :
      (fun index => abs (tailTerms
        (constantCoefficients dimension constant) displacement index)) =
      (fun _ : Nat => zero) := by
    funext index
    rw [constant_tail_zero, abs_zero]
  rw [equal, partial_sum_zero_terms]
  exact le_refl zero

public theorem shellMagnitude_zero_of_coefficients
    {dimension degreeValue : Nat}
    {coefficients : MultiIndex.carrier dimension → selection.Carrier}
    (displacement : FiniteVector.carrier dimension)
    (zeroOn : ∀ index,
      index ∈ MultiIndex.degreeShell dimension degreeValue →
        coefficients index = zero) :
    shellMagnitude coefficients displacement degreeValue = zero := by
  unfold shellMagnitude
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices → coefficients index = zero) →
      indices.foldr
        (fun index total => add (abs (mul (coefficients index)
          (MultiIndex.monomial dimension index displacement))) total)
        zero = zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro vanished
        simp only [List.foldr_cons, vanished index (List.mem_cons_self),
          zero_mul, abs_zero, zero_add]
        apply induction
        intro later member
        exact vanished later (List.mem_cons_of_mem index member)
  exact go (MultiIndex.degreeShell dimension degreeValue) zeroOn

public theorem constant_tailMagnitudes_zero (dimension : Nat)
    (constant : selection.Carrier)
    (displacement : FiniteVector.carrier dimension) (degreeValue : Nat) :
    tailMagnitudes (constantCoefficients dimension constant)
      displacement degreeValue = zero := by
  apply shellMagnitude_zero_of_coefficients
  intro index member
  have degreeEqual := MultiIndex.degree_of_mem_shell member
  simp only [constantCoefficients, degreeEqual]
  simp

/-- Degreewise absolute coefficient sums have bounded partial sums. -/
@[expose] public def NormallyConvergent {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension) : Prop :=
  ∃ upper : selection.Carrier,
    ∀ count, le (partialSum (tailMagnitudes coefficients displacement) count)
      upper

public theorem constant_normal (dimension : Nat)
    (constant : selection.Carrier)
    (displacement : FiniteVector.carrier dimension) :
    NormallyConvergent (constantCoefficients dimension constant)
      displacement := by
  refine ⟨zero, fun count => ?_⟩
  have equal : tailMagnitudes
      (constantCoefficients dimension constant) displacement =
      (fun _ : Nat => zero) := by
    funext index
    exact constant_tailMagnitudes_zero dimension constant displacement index
  rw [equal, partial_sum_zero_terms]
  exact le_refl zero

public theorem coordinate_normal {dimension : Nat}
    (selected : Fin dimension)
    (displacement : FiniteVector.carrier dimension) :
    NormallyConvergent (coordinateCoefficients selected) displacement := by
  refine ⟨abs (displacement selected), fun count => ?_⟩
  let values := tailMagnitudes (coordinateCoefficients selected) displacement
  have zeroAfter : ∀ index, 1 ≤ index → values index = zero := by
    intro index later
    cases index with
    | zero => omega
    | succ index => exact coordinate_tail_magnitude_succ selected displacement index
  cases count with
  | zero =>
      rw [partial_sum_zero]
      exact abs_nonnegative (displacement selected)
  | succ count =>
      have later : 1 ≤ count + 1 := by omega
      rw [partial_sum_zero_after zeroAfter later,
        partial_sum_succ, partial_sum_zero, zero_add]
      change le
        (tailMagnitudes (coordinateCoefficients selected) displacement 0)
        (abs (displacement selected))
      rw [coordinate_tail_magnitude_zero]
      exact le_refl _

public theorem normally_convergent_add {dimension : Nat}
    {first second : MultiIndex.carrier dimension → selection.Carrier}
    {displacement : FiniteVector.carrier dimension}
    (firstNormal : NormallyConvergent first displacement)
    (secondNormal : NormallyConvergent second displacement) :
    NormallyConvergent
      (fun index => add (first index) (second index)) displacement := by
  rcases firstNormal with ⟨firstUpper, firstBound⟩
  rcases secondNormal with ⟨secondUpper, secondBound⟩
  refine ⟨add firstUpper secondUpper, fun count => ?_⟩
  exact le_trans
    (partial_sum_le
      (tailMagnitudes_add_le first second displacement) count)
    (by
      rw [partial_sum_add]
      exact add_le_add (firstBound count) (secondBound count))

/-- A coefficient family with an absolutely convergent local evaluation. -/
public structure Convergent (dimension : Nat) where
  coefficients : MultiIndex.carrier dimension → selection.Carrier
  radius : selection.Carrier
  radiusPositive : lt zero radius
  normalOn : ∀ displacement : FiniteVector.carrier dimension,
    FiniteVector.ball (FiniteVector.zeroVector dimension) radius displacement →
      NormallyConvergent coefficients displacement

public theorem Convergent.absoluteOn {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    AbsolutelySummable (tailTerms series.coefficients displacement) := by
  rcases series.normalOn displacement inside with ⟨upper, bound⟩
  refine ⟨upper, fun count => ?_⟩
  exact le_trans
    (partial_sum_le
      (fun degreeValue => abs_shellTerm_le_magnitude
        series.coefficients displacement (degreeValue + 1)) count)
    (bound count)

/-- One point on the positive diagonal supplies a common majorant for all
coefficientwise absolute partial sums in a smaller closed coordinate box. -/
public theorem Convergent.normal_bounded_closed_ball {dimension : Nat}
    (series : Convergent dimension)
    {radius : selection.Carrier} (positive : lt zero radius)
    (smaller : lt radius series.radius) :
    ∃ upper : selection.Carrier,
      ∀ displacement : FiniteVector.carrier dimension,
        (∀ coordinate, le (abs (displacement coordinate)) radius) →
        ∀ count,
          le (partialSum
              (tailMagnitudes series.coefficients displacement) count)
            upper := by
  have diagonalInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius) := by
    intro coordinate
    change lt (abs (sub radius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative positive.left]
    exact smaller
  rcases series.normalOn (fun _ => radius) diagonalInside with
    ⟨upper, bound⟩
  refine ⟨upper, fun displacement coordinates count => ?_⟩
  exact le_trans
    (partial_sum_le
      (fun degreeValue => tailMagnitudes_le_constant
        series.coefficients displacement positive.left coordinates
        degreeValue) count)
    (bound count)

/-- Every positive smaller closed coordinate box has one Cauchy stage for all
series tails. This is the uniform convergence estimate needed for local
analytic calculus. -/
public theorem Convergent.uniform_tails_closed_ball {dimension : Nat}
    (series : Convergent dimension)
    {radius : selection.Carrier} (positive : lt zero radius)
    (smaller : lt radius series.radius)
    {tolerance : selection.Carrier} (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat,
      ∀ displacement : FiniteVector.carrier dimension,
        (∀ coordinate, le (abs (displacement coordinate)) radius) →
        ∀ start, stage ≤ start → ∀ count,
          lt (abs (partialSum
            (fun index => tailTerms series.coefficients displacement
              (start + index)) count)) tolerance := by
  let diagonal : FiniteVector.carrier dimension := fun _ => radius
  let magnitudes := tailMagnitudes series.coefficients diagonal
  have diagonalInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius diagonal := by
    intro coordinate
    change lt (abs (sub radius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative positive.left]
    exact smaller
  rcases series.normalOn diagonal diagonalInside with ⟨upper, bound⟩
  have diagonalSummable : Summable magnitudes :=
    summable_of_nonnegative_bounded
      (fun index => shellMagnitude_nonnegative
        series.coefficients diagonal (index + 1))
      ⟨upper, bound⟩
  rcases (summable_cauchy diagonalSummable) tolerance tolerancePositive with
    ⟨stage, close⟩
  refine ⟨stage, fun displacement coordinates start later count => ?_⟩
  have signedBound := abs_partial_sum_le
    (fun index => tailTerms series.coefficients displacement
      (start + index)) count
  have shellBound : le
      (partialSum
        (fun index => abs (tailTerms series.coefficients displacement
          (start + index))) count)
      (partialSum
        (fun index => tailMagnitudes series.coefficients displacement
          (start + index)) count) :=
    partial_sum_le
      (fun index => abs_shellTerm_le_magnitude series.coefficients
        displacement (start + index + 1)) count
  have radiusBound : le
      (partialSum
        (fun index => tailMagnitudes series.coefficients displacement
          (start + index)) count)
      (partialSum (fun index => magnitudes (start + index)) count) :=
    partial_sum_le
      (fun index => tailMagnitudes_le_constant
        series.coefficients displacement positive.left coordinates
        (start + index)) count
  have tailIdentity :
      partialSum (fun index => magnitudes (start + index)) count =
        sub (partialSum magnitudes (start + count))
          (partialSum magnitudes start) := by
    have append := partial_sum_append magnitudes start count
    rw [append, add_sub_self]
  have closeTail := close (start + count) start
    (Nat.le_trans later (Nat.le_add_right _ _)) later
  rw [← tailIdentity] at closeTail
  exact lt_of_le_of_lt
    (le_trans (le_trans (le_trans signedBound shellBound) radiusBound)
      (le_abs _)) closeTail

public theorem converges_to_offset {values : Nat → selection.Carrier}
    {limit : selection.Carrier} (converges : ConvergesTo values limit)
    (offset : Nat) :
    ConvergesTo (fun index => values (offset + index)) limit := by
  intro tolerance positive
  rcases converges tolerance positive with ⟨stage, close⟩
  refine ⟨stage, fun index later => close (offset + index) ?_⟩
  omega

public theorem partial_sum_tail_converges
    (values : Nat → selection.Carrier) (certificate : Summable values)
    (offset : Nat) :
    ConvergesTo
      (partialSum (fun index => values (offset + index)))
      (sub (sum values certificate) (partialSum values offset)) := by
  have shifted := converges_to_offset
    (partial_sum_converges values certificate) offset
  have difference := converges_to_sub shifted
    (converges_to_const (partialSum values offset))
  have equal :
      (fun index => sub (partialSum values (offset + index))
        (partialSum values offset)) =
      partialSum (fun index => values (offset + index)) := by
    funext index
    rw [partial_sum_append, add_sub_self]
  rw [equal] at difference
  exact difference

/-- The degree partial sums approach the signed series value uniformly on
each smaller closed coordinate box. -/
public theorem Convergent.uniform_sum_closed_ball {dimension : Nat}
    (series : Convergent dimension)
    {radius : selection.Carrier} (positive : lt zero radius)
    (smaller : lt radius series.radius)
    {tolerance : selection.Carrier} (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat,
      ∀ displacement : FiniteVector.carrier dimension,
        ∀ inside : FiniteVector.ball
          (FiniteVector.zeroVector dimension) series.radius displacement,
        (∀ coordinate, le (abs (displacement coordinate)) radius) →
        ∀ count, stage ≤ count →
          lt (abs (sub
            (partialSum (tailTerms series.coefficients displacement) count)
            (sum (tailTerms series.coefficients displacement)
              (summable_of_absolute_bound
                (series.absoluteOn displacement inside))))) tolerance := by
  have halfPositive := half_positive tolerancePositive
  rcases series.uniform_tails_closed_ball positive smaller halfPositive with
    ⟨stage, tails⟩
  have halfBelow : lt (half tolerance) tolerance := by
    have raised := add_lt_add_left (half tolerance) halfPositive
    rwa [add_zero, add_half] at raised
  refine ⟨stage, fun displacement inside coordinates count later => ?_⟩
  let values := tailTerms series.coefficients displacement
  let certificate := summable_of_absolute_bound
    (series.absoluteOn displacement inside)
  have tailLimit := partial_sum_tail_converges values certificate count
  have tailBound : ∀ length,
      le (abs (partialSum (fun index => values (count + index)) length))
        (half tolerance) := by
    intro length
    exact le_of_lt (tails displacement coordinates count later length)
  have limitBound := abs_le_of_convergesTo tailLimit tailBound
  change lt (abs (sub (partialSum values count) (sum values certificate)))
    tolerance
  rw [abs_sub_comm (partialSum values count) (sum values certificate)]
  exact lt_of_le_of_lt limitBound halfBelow

@[expose] public def constantSeries (dimension : Nat)
    (constant radius : selection.Carrier) (positive : lt zero radius) :
    Convergent dimension where
  coefficients := constantCoefficients dimension constant
  radius := radius
  radiusPositive := positive
  normalOn := fun displacement _ => constant_normal dimension constant displacement

@[expose] public def coordinateSeries {dimension : Nat}
    (selected : Fin dimension)
    (radius : selection.Carrier) (positive : lt zero radius) :
    Convergent dimension where
  coefficients := coordinateCoefficients selected
  radius := radius
  radiusPositive := positive
  normalOn := fun displacement _ => coordinate_normal selected displacement

/-- Add two convergent series on a common smaller ball. -/
@[expose] public noncomputable def addSeries {dimension : Nat}
    (first second : Convergent dimension) : Convergent dimension := by
  let witness := small_positive first.radiusPositive second.radiusPositive
  let commonRadius := Classical.choose witness
  have radiusFacts := Classical.choose_spec witness
  refine {
    coefficients := fun index => add (first.coefficients index)
      (second.coefficients index)
    radius := commonRadius
    radiusPositive := radiusFacts.left
    normalOn := ?_
  }
  intro displacement inside
  have firstInside := FiniteVector.ball_mono radiusFacts.right.left inside
  have secondInside := FiniteVector.ball_mono radiusFacts.right.right inside
  exact normally_convergent_add
    (first.normalOn displacement firstInside)
    (second.normalOn displacement secondInside)

@[expose] public def scaleSeries {dimension : Nat}
    (factor : selection.Carrier) (series : Convergent dimension) :
    Convergent dimension where
  coefficients := fun index => mul factor (series.coefficients index)
  radius := series.radius
  radiusPositive := series.radiusPositive
  normalOn := by
    intro displacement inside
    rcases series.normalOn displacement inside with ⟨upper, bound⟩
    refine ⟨mul (abs factor) upper, fun count => ?_⟩
    have termsEqual :
        tailMagnitudes (fun index => mul factor (series.coefficients index))
          displacement =
        (fun index => mul (abs factor)
          (tailMagnitudes series.coefficients displacement index)) := by
      funext index
      exact tailMagnitudes_scale factor series.coefficients
        displacement index
    rw [termsEqual, partial_sum_scale]
    exact mul_le_mul_nonnegative_left (bound count)
      (abs_nonnegative factor)

/-- A smaller positive radius keeps the same coefficient family and value. -/
@[expose] public def restrictRadius {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (included : le radius series.radius) : Convergent dimension where
  coefficients := series.coefficients
  radius := radius
  radiusPositive := positive
  normalOn := fun displacement inside =>
    series.normalOn displacement
      (FiniteVector.ball_mono included inside)

public theorem addSeries_radius_le_first {dimension : Nat}
    (first second : Convergent dimension) :
    le (addSeries first second).radius first.radius :=
  (Classical.choose_spec
    (small_positive first.radiusPositive second.radiusPositive)).right.left

public theorem addSeries_radius_le_second {dimension : Nat}
    (first second : Convergent dimension) :
    le (addSeries first second).radius second.radius :=
  (Classical.choose_spec
    (small_positive first.radiusPositive second.radiusPositive)).right.right

/-- Evaluate a series inside its certified common-radius ball. -/
@[expose] public noncomputable def value {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    selection.Carrier :=
  add (series.coefficients (MultiIndex.zeroIndex dimension))
    (sum (tailTerms series.coefficients displacement)
      (summable_of_absolute_bound (series.absoluteOn displacement inside)))

public theorem constantSeries_value (dimension : Nat)
    (constant radius : selection.Carrier) (positive : lt zero radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    value (constantSeries dimension constant radius positive)
      displacement inside = constant := by
  let terms := tailTerms (constantCoefficients dimension constant) displacement
  have termsZero : terms = fun _ : Nat => zero := by
    funext index
    exact constant_tail_zero dimension constant displacement index
  have partialZero : (fun count => partialSum terms count) =
      (fun _ : Nat => zero) := by
    funext count
    rw [termsZero, partial_sum_zero_terms]
  have converges : ConvergesTo (partialSum terms) zero := by
    change ConvergesTo (fun count => partialSum terms count) zero
    rw [partialZero]
    exact converges_to_const zero
  have totalZero : sum terms
      (summable_of_absolute_bound
        (constant_absolute dimension constant displacement)) = zero :=
    sum_eq_of_converges terms _ converges
  unfold value constantSeries
  change add (constantCoefficients dimension constant
      (MultiIndex.zeroIndex dimension))
    (sum terms (summable_of_absolute_bound
      (constant_absolute dimension constant displacement))) = constant
  rw [totalZero, add_zero]
  simp only [constantCoefficients, MultiIndex.degree_zeroIndex, ↓reduceIte]

public theorem coordinateSeries_value {dimension : Nat}
    (selected : Fin dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    value (coordinateSeries selected radius positive)
      displacement inside = displacement selected := by
  let terms := tailTerms (coordinateCoefficients selected) displacement
  have zeroAfter : ∀ index, 1 ≤ index → terms index = zero := by
    intro index later
    cases index with
    | zero => omega
    | succ index => exact coordinate_tail_succ selected displacement index
  have converges : ConvergesTo (partialSum terms)
      (displacement selected) := by
    intro tolerance tolerancePositive
    refine ⟨1, fun count later => ?_⟩
    rw [partial_sum_zero_after zeroAfter later,
      partial_sum_succ, partial_sum_zero, zero_add]
    change lt (abs (sub
      (tailTerms (coordinateCoefficients selected) displacement 0)
      (displacement selected))) tolerance
    rw [coordinate_tail_zero, sub_self, abs_zero]
    exact tolerancePositive
  have total : sum terms
      (summable_of_absolute_bound
        ((coordinateSeries selected radius positive).absoluteOn
          displacement inside)) = displacement selected :=
    sum_eq_of_converges terms _ converges
  have zeroDistinct :
      MultiIndex.zeroIndex dimension ≠ MultiIndex.unitIndex selected := by
    intro equal
    have degrees := congrArg (MultiIndex.degree dimension) equal
    rw [MultiIndex.degree_zeroIndex,
      MultiIndex.degree_unitIndex] at degrees
    omega
  unfold value coordinateSeries
  change add (coordinateCoefficients selected
      (MultiIndex.zeroIndex dimension))
    (sum terms
      (summable_of_absolute_bound
        ((coordinateSeries selected radius positive).absoluteOn
          displacement inside))) = displacement selected
  rw [total]
  simp [coordinateCoefficients, zeroDistinct, zero_add]

private theorem sum_congr {first second : Nat → selection.Carrier}
    (equal : first = second)
    (firstSummable : Summable first) (secondSummable : Summable second) :
    sum first firstSummable = sum second secondSummable := by
  cases equal
  rfl

public theorem addSeries_value {dimension : Nat}
    (first second : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension)
      (addSeries first second).radius displacement) :
    value (addSeries first second) displacement inside =
      add
        (value first displacement
          (FiniteVector.ball_mono
            (addSeries_radius_le_first first second) inside))
        (value second displacement
          (FiniteVector.ball_mono
            (addSeries_radius_le_second first second) inside)) := by
  have firstInside := FiniteVector.ball_mono
    (addSeries_radius_le_first first second) inside
  have secondInside := FiniteVector.ball_mono
    (addSeries_radius_le_second first second) inside
  have termsEqual :
      tailTerms (addSeries first second).coefficients displacement =
      (fun degreeValue => add
        (tailTerms first.coefficients displacement degreeValue)
        (tailTerms second.coefficients displacement degreeValue)) := by
    funext degreeValue
    exact tailTerms_add first.coefficients second.coefficients
      displacement degreeValue
  have seriesEqual :
      sum (tailTerms (addSeries first second).coefficients displacement)
        (summable_of_absolute_bound
          ((addSeries first second).absoluteOn displacement inside)) =
      add
        (sum (tailTerms first.coefficients displacement)
          (summable_of_absolute_bound
            (first.absoluteOn displacement firstInside)))
        (sum (tailTerms second.coefficients displacement)
          (summable_of_absolute_bound
            (second.absoluteOn displacement secondInside))) := by
    let firstSummable := summable_of_absolute_bound
      (first.absoluteOn displacement firstInside)
    let secondSummable := summable_of_absolute_bound
      (second.absoluteOn displacement secondInside)
    calc
      sum (tailTerms (addSeries first second).coefficients displacement)
          (summable_of_absolute_bound
            ((addSeries first second).absoluteOn displacement inside)) =
        sum (fun degreeValue => add
          (tailTerms first.coefficients displacement degreeValue)
          (tailTerms second.coefficients displacement degreeValue))
          (summable_add firstSummable secondSummable) :=
        sum_congr termsEqual _ _
      _ = add
          (sum (tailTerms first.coefficients displacement) firstSummable)
          (sum (tailTerms second.coefficients displacement) secondSummable) :=
        sum_add firstSummable secondSummable
  unfold value
  change add (add (first.coefficients (MultiIndex.zeroIndex dimension))
      (second.coefficients (MultiIndex.zeroIndex dimension)))
      (sum (tailTerms (addSeries first second).coefficients displacement)
        (summable_of_absolute_bound
          ((addSeries first second).absoluteOn displacement inside))) =
    add
      (add (first.coefficients (MultiIndex.zeroIndex dimension))
        (sum (tailTerms first.coefficients displacement)
          (summable_of_absolute_bound
            (first.absoluteOn displacement firstInside))))
      (add (second.coefficients (MultiIndex.zeroIndex dimension))
        (sum (tailTerms second.coefficients displacement)
          (summable_of_absolute_bound
            (second.absoluteOn displacement secondInside))))
  rw [seriesEqual]
  ac_rfl

public theorem scaleSeries_value {dimension : Nat}
    (factor : selection.Carrier) (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    value (scaleSeries factor series) displacement inside =
      mul factor (value series displacement inside) := by
  have termsEqual :
      tailTerms (scaleSeries factor series).coefficients displacement =
      (fun index => mul factor
        (tailTerms series.coefficients displacement index)) := by
    funext index
    exact tailTerms_scale factor series.coefficients displacement index
  have baseSummable := summable_of_absolute_bound
    (series.absoluteOn displacement inside)
  have seriesEqual :
      sum (tailTerms (scaleSeries factor series).coefficients displacement)
        (summable_of_absolute_bound
          ((scaleSeries factor series).absoluteOn displacement inside)) =
      mul factor (sum (tailTerms series.coefficients displacement)
        baseSummable) := by
    calc
      sum (tailTerms (scaleSeries factor series).coefficients displacement)
          (summable_of_absolute_bound
            ((scaleSeries factor series).absoluteOn displacement inside)) =
        sum (fun index => mul factor
          (tailTerms series.coefficients displacement index))
          (summable_scale factor baseSummable) :=
        sum_congr termsEqual _ _
      _ = mul factor
          (sum (tailTerms series.coefficients displacement) baseSummable) :=
        sum_scale factor baseSummable
  unfold value
  change add (mul factor
      (series.coefficients (MultiIndex.zeroIndex dimension)))
      (sum (tailTerms (scaleSeries factor series).coefficients displacement)
        (summable_of_absolute_bound
          ((scaleSeries factor series).absoluteOn displacement inside))) =
    mul factor
      (add (series.coefficients (MultiIndex.zeroIndex dimension))
        (sum (tailTerms series.coefficients displacement) baseSummable))
  rw [seriesEqual, mul_add]

public theorem restrictRadius_value {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (included : le radius series.radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    value (restrictRadius series radius positive included)
      displacement inside =
    value series displacement (FiniteVector.ball_mono included inside) := by
  rfl

/-- Analyticity is a local convergent power-series representation on an open
domain. This is the representation side of the ωPAP definition. -/
@[expose] public def AnalyticOn {dimension : Nat}
    (region : FiniteVector.carrier dimension → Prop)
    (function : FiniteVector.carrier dimension → selection.Carrier) : Prop :=
  FiniteVector.IsOpen region ∧
    ∀ center, region center →
      ∃ series : Convergent dimension,
        (∀ point, FiniteVector.ball center series.radius point →
          region point) ∧
        (∀ point (inside : FiniteVector.ball center series.radius point),
          function point = value series (FiniteVector.subVector point center)
            (by
              intro coordinate
              simpa only [FiniteVector.ball, FiniteVector.zeroVector,
                FiniteVector.subVector, sub_zero] using inside coordinate))

/-- Constants admit a convergent local Taylor representation on every open
domain. -/
public theorem analytic_on_constant {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (constant : selection.Carrier) :
    AnalyticOn region (fun _ => constant) := by
  refine ⟨openRegion, fun center member => ?_⟩
  rcases openRegion center member with ⟨radius, positive, within⟩
  refine ⟨constantSeries dimension constant radius positive, within, ?_⟩
  intro point inside
  exact (constantSeries_value dimension constant radius positive
    (FiniteVector.subVector point center) _).symm

/-- Each coordinate projection has its linear Taylor series on any open
domain. -/
public theorem analytic_on_coordinate {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (selected : Fin dimension) :
    AnalyticOn region (fun point => point selected) := by
  refine ⟨openRegion, fun center member => ?_⟩
  rcases openRegion center member with ⟨radius, positive, within⟩
  let constantPart := constantSeries dimension (center selected) radius positive
  let linearPart := coordinateSeries selected radius positive
  let series := addSeries constantPart linearPart
  have radiusBound : le series.radius radius :=
    addSeries_radius_le_first constantPart linearPart
  refine ⟨series, ?_, ?_⟩
  · intro point inside
    exact within point (FiniteVector.ball_mono radiusBound inside)
  · intro point inside
    have displacedInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (FiniteVector.subVector point center) := by
      intro coordinate
      simpa only [FiniteVector.ball, FiniteVector.zeroVector,
        FiniteVector.subVector, sub_zero] using inside coordinate
    change point selected =
      value series (FiniteVector.subVector point center) displacedInside
    rw [addSeries_value constantPart linearPart
      (FiniteVector.subVector point center) displacedInside,
      constantSeries_value, coordinateSeries_value]
    exact (add_sub_cancel (point selected) (center selected)).symm

/-- Analytic local representations are closed under pointwise addition. -/
public theorem analytic_on_add {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {first second : FiniteVector.carrier dimension → selection.Carrier}
    (firstAnalytic : AnalyticOn region first)
    (secondAnalytic : AnalyticOn region second) :
    AnalyticOn region (fun point => add (first point) (second point)) := by
  refine ⟨firstAnalytic.left, fun center member => ?_⟩
  rcases firstAnalytic.right center member with
    ⟨firstSeries, firstWithin, firstAgree⟩
  rcases secondAnalytic.right center member with
    ⟨secondSeries, _, secondAgree⟩
  refine ⟨addSeries firstSeries secondSeries, ?_, ?_⟩
  · intro point inside
    exact firstWithin point
      (FiniteVector.ball_mono
        (addSeries_radius_le_first firstSeries secondSeries) inside)
  · intro point inside
    have firstInside := FiniteVector.ball_mono
      (addSeries_radius_le_first firstSeries secondSeries) inside
    have secondInside := FiniteVector.ball_mono
      (addSeries_radius_le_second firstSeries secondSeries) inside
    have displacedInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension)
        (addSeries firstSeries secondSeries).radius
        (FiniteVector.subVector point center) := by
      intro coordinate
      simpa only [FiniteVector.ball, FiniteVector.zeroVector,
        FiniteVector.subVector, sub_zero] using inside coordinate
    change add (first point) (second point) =
      value (addSeries firstSeries secondSeries)
        (FiniteVector.subVector point center) displacedInside
    rw [firstAgree point firstInside, secondAgree point secondInside]
    exact (addSeries_value firstSeries secondSeries
      (FiniteVector.subVector point center) displacedInside).symm

public theorem analytic_on_scale {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (factor : selection.Carrier) :
    AnalyticOn region (fun point => mul factor (function point)) := by
  refine ⟨analytic.left, fun center member => ?_⟩
  rcases analytic.right center member with ⟨series, within, agree⟩
  refine ⟨scaleSeries factor series, within, ?_⟩
  intro point inside
  change mul factor (function point) =
    value (scaleSeries factor series)
      (FiniteVector.subVector point center) _
  rw [agree point inside]
  exact (scaleSeries_value factor series
    (FiniteVector.subVector point center) _).symm

/-- An analytic representation restricts to an open subdomain. -/
public theorem analytic_on_open_subset {dimension : Nat}
    {large small : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn large function)
    (openSmall : FiniteVector.IsOpen small)
    (included : ∀ point, small point → large point) :
    AnalyticOn small function := by
  refine ⟨openSmall, fun center member => ?_⟩
  rcases analytic.right center (included center member) with
    ⟨series, _, agree⟩
  rcases openSmall center member with
    ⟨smallRadius, smallPositive, smallWithin⟩
  rcases small_positive series.radiusPositive smallPositive with
    ⟨radius, positive, seriesBound, smallBound⟩
  let smallerSeries := restrictRadius series radius positive seriesBound
  refine ⟨smallerSeries, ?_, ?_⟩
  · intro point inside
    exact smallWithin point (FiniteVector.ball_mono smallBound inside)
  · intro point inside
    have seriesInside := FiniteVector.ball_mono seriesBound inside
    rw [agree point seriesInside]
    exact (restrictRadius_value series radius positive seriesBound
      (FiniteVector.subVector point center) _).symm

end

end Problib.Analysis.Real.PowerSeries
