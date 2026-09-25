module

public import Problib.Analysis.Real.PowerSeries.DerivativeExchange

/-! Reindex differentiated homogeneous shells by their lowered multiindex. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨add_assoc⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

public theorem monomialSliceDerivative_zero_coordinate_any
    (dimension : Nat) (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (vanished : index selected = 0) :
    monomialSliceDerivative dimension index point selected = zero := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          change mul (powerDerivative (point 0) (index 0))
            (MultiIndex.monomial dimension
              (fun coordinate => index coordinate.succ)
              (fun coordinate => point coordinate.succ)) = zero
          rw [vanished]
          change mul zero _ = zero
          rw [zero_mul]
      | succ selected =>
          change mul (power (point 0) (index 0))
            (monomialSliceDerivative dimension
              (fun coordinate => index coordinate.succ)
              (fun coordinate => point coordinate.succ)
              selected) = zero
          rw [induction (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ) selected vanished,
            mul_zero]

public theorem monomialSliceDerivative_positive_formula
    (dimension : Nat) (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension)
    (positive : 0 < index selected) :
    monomialSliceDerivative dimension index point selected =
      mul (naturalScale (index selected))
        (MultiIndex.monomial dimension
          (MultiIndex.subIndex index (MultiIndex.unitIndex selected))
          point) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      let tailIndex : MultiIndex.carrier dimension :=
        fun coordinate => index coordinate.succ
      let tailPoint : FiniteVector.carrier dimension :=
        fun coordinate => point coordinate.succ
      cases selected using Fin.cases with
      | zero =>
          obtain ⟨count, head⟩ : ∃ count, index 0 = count + 1 := by
            cases value : index 0 with
            | zero => omega
            | succ count => exact ⟨count, rfl⟩
          have subHead :
              (MultiIndex.subIndex index
                (MultiIndex.unitIndex (0 : Fin (dimension + 1)))) 0 =
              count := by
            simp [MultiIndex.subIndex, MultiIndex.unitIndex, head]
          have subTail :
              (fun coordinate : Fin dimension =>
                (MultiIndex.subIndex index
                  (MultiIndex.unitIndex (0 : Fin (dimension + 1))))
                  coordinate.succ) = tailIndex := by
            funext coordinate
            have distinct : coordinate.succ ≠
                (0 : Fin (dimension + 1)) := Fin.succ_ne_zero coordinate
            simp [MultiIndex.subIndex, MultiIndex.unitIndex,
              tailIndex, distinct]
          change mul (powerDerivative (point 0) (index 0))
              (MultiIndex.monomial dimension tailIndex tailPoint) =
            mul (naturalScale (index 0))
              (mul (power (point 0)
                ((MultiIndex.subIndex index
                  (MultiIndex.unitIndex (0 : Fin (dimension + 1)))) 0))
                (MultiIndex.monomial dimension
                  (fun coordinate =>
                    (MultiIndex.subIndex index
                      (MultiIndex.unitIndex (0 : Fin (dimension + 1))))
                      coordinate.succ) tailPoint))
          rw [head, subHead, subTail, powerDerivative_succ,
            mul_assoc]
      | succ selected =>
          have headZero : MultiIndex.unitIndex selected.succ
              (0 : Fin (dimension + 1)) = 0 := by
            have distinct : (0 : Fin (dimension + 1)) ≠
                selected.succ :=
              fun equal => Fin.succ_ne_zero selected equal.symm
            simp [MultiIndex.unitIndex, distinct]
          have tailUnit :
              (fun coordinate : Fin dimension =>
                MultiIndex.unitIndex selected.succ coordinate.succ) =
              MultiIndex.unitIndex selected := by
            funext coordinate
            simp [MultiIndex.unitIndex]
          have subHead :
              (MultiIndex.subIndex index
                (MultiIndex.unitIndex selected.succ)) 0 = index 0 := by
            simp [MultiIndex.subIndex, headZero]
          have subTail :
              (fun coordinate : Fin dimension =>
                (MultiIndex.subIndex index
                  (MultiIndex.unitIndex selected.succ)) coordinate.succ) =
              MultiIndex.subIndex tailIndex
                (MultiIndex.unitIndex selected) := by
            funext coordinate
            change index coordinate.succ -
                MultiIndex.unitIndex selected.succ coordinate.succ =
              index coordinate.succ -
                MultiIndex.unitIndex selected coordinate
            rw [congrFun tailUnit coordinate]
          change mul (power (point 0) (index 0))
              (monomialSliceDerivative dimension tailIndex tailPoint
                selected) =
            mul (naturalScale (index selected.succ))
              (mul (power (point 0)
                ((MultiIndex.subIndex index
                  (MultiIndex.unitIndex selected.succ)) 0))
                (MultiIndex.monomial dimension
                  (fun coordinate =>
                    (MultiIndex.subIndex index
                      (MultiIndex.unitIndex selected.succ)) coordinate.succ)
                  tailPoint))
          rw [subHead, subTail,
            induction tailIndex tailPoint selected positive]
          ac_rfl

private theorem nodup_perm_of_mem_iff {α : Type}
    [DecidableEq α] {first second : List α}
    (firstNodup : first.Nodup) (secondNodup : second.Nodup)
    (same : ∀ item, item ∈ first ↔ item ∈ second) :
    first.Perm second := by
  classical
  apply List.perm_iff_count.mpr
  intro item
  rw [firstNodup.count, secondNodup.count]
  simp [same item]

private theorem add_unit_injective {dimension : Nat}
    (selected : Fin dimension) :
    Function.Injective (fun index : MultiIndex.carrier dimension =>
      MultiIndex.addIndex index (MultiIndex.unitIndex selected)) := by
  intro first second equal
  funext coordinate
  have coordinateEqual := congrFun equal coordinate
  simp only [MultiIndex.addIndex] at coordinateEqual
  omega

private theorem added_unit_selected_positive {dimension : Nat}
    (selected : Fin dimension) (index : MultiIndex.carrier dimension) :
    0 < MultiIndex.addIndex index
      (MultiIndex.unitIndex selected) selected := by
  simp [MultiIndex.addIndex, MultiIndex.unitIndex]

private theorem unit_included_of_selected_positive {dimension : Nat}
    (selected : Fin dimension) (index : MultiIndex.carrier dimension)
    (positive : 0 < index selected) :
    MultiIndex.LeIndex (MultiIndex.unitIndex selected) index := by
  intro coordinate
  by_cases same : coordinate = selected
  · subst coordinate
    simpa [MultiIndex.unitIndex] using (Nat.succ_le_of_lt positive)
  · simp [MultiIndex.unitIndex, same]

private theorem shell_positive_perm_added_unit {dimension degreeValue : Nat}
    (selected : Fin dimension) :
    ((MultiIndex.degreeShell dimension (degreeValue + 1)).filter
      (fun index => 0 < index selected)).Perm
    ((MultiIndex.degreeShell dimension degreeValue).map
      (fun index => MultiIndex.addIndex index
        (MultiIndex.unitIndex selected))) := by
  classical
  apply nodup_perm_of_mem_iff
  · exact (MultiIndex.degreeShell_nodup dimension (degreeValue + 1)).filter _
  · apply (List.pairwise_map).mpr
    apply (MultiIndex.degreeShell_nodup dimension degreeValue).imp
    intro first second distinct equal
    exact distinct ((add_unit_injective selected) equal)
  intro index
  constructor
  · intro member
    have shellMember := (List.mem_filter.mp member).1
    have positive := of_decide_eq_true (List.mem_filter.mp member).2
    have included := unit_included_of_selected_positive selected index positive
    have sourceDegree :
        MultiIndex.degree dimension
          (MultiIndex.subIndex index (MultiIndex.unitIndex selected)) =
          degreeValue := by
      rw [MultiIndex.degree_subIndex included,
        MultiIndex.degree_of_mem_shell shellMember,
        MultiIndex.degree_unitIndex]
      omega
    apply List.mem_map.mpr
    refine ⟨MultiIndex.subIndex index (MultiIndex.unitIndex selected),
      (MultiIndex.mem_degreeShell_iff).mpr sourceDegree, ?_⟩
    funext coordinate
    exact Nat.sub_add_cancel (included coordinate)
  · intro member
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    subst index
    apply List.mem_filter.mpr
    constructor
    · apply (MultiIndex.mem_degreeShell_iff).mpr
      rw [MultiIndex.degree_addIndex,
        MultiIndex.degree_of_mem_shell sourceMember,
        MultiIndex.degree_unitIndex]
    · exact decide_eq_true (added_unit_selected_positive selected source)

private theorem foldr_filter_zero {α : Type} (indices : List α)
    (keep : α → Bool) (value : α → selection.Carrier)
    (vanishes : ∀ index ∈ indices, keep index = false → value index = zero) :
    indices.foldr (fun index total => add (value index) total) zero =
      (indices.filter keep).foldr
        (fun index total => add (value index) total) zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      by_cases selected : keep index = true
      · simp only [List.foldr_cons, List.filter_cons, selected, ↓reduceIte]
        exact congrArg (add (value index))
          (induction (fun later member => vanishes later
            (List.mem_cons_of_mem index member)))
      · have excluded : keep index = false := by
          cases value : keep index <;> simp_all
        simp only [List.foldr_cons, List.filter_cons, excluded]
        rw [vanishes index List.mem_cons_self excluded, zero_add]
        exact induction (fun later member => vanishes later
          (List.mem_cons_of_mem index member))

private theorem derivative_term_zero {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (index : MultiIndex.carrier dimension)
    (vanished : index selected = 0) :
    mul (coefficients index)
      (monomialSliceDerivative dimension index point selected) = zero := by
  rw [monomialSliceDerivative_zero_coordinate_any
    dimension index point selected vanished, mul_zero]

private theorem derivative_term_positive {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (index : MultiIndex.carrier dimension)
    (positive : 0 < index selected) :
    mul (coefficients index)
      (monomialSliceDerivative dimension index point selected) =
    mul (partialDerivativeCoefficients selected coefficients
      (MultiIndex.subIndex index (MultiIndex.unitIndex selected)))
      (MultiIndex.monomial dimension
        (MultiIndex.subIndex index (MultiIndex.unitIndex selected)) point) := by
  have included := unit_included_of_selected_positive selected index positive
  have restored :
      MultiIndex.addIndex
        (MultiIndex.subIndex index (MultiIndex.unitIndex selected))
        (MultiIndex.unitIndex selected) = index := by
    funext coordinate
    exact Nat.sub_add_cancel (included coordinate)
  have exponent :
      (MultiIndex.subIndex index (MultiIndex.unitIndex selected)) selected
        + 1 = index selected := by
    simp only [MultiIndex.subIndex, MultiIndex.unitIndex, ↓reduceIte]
    omega
  rw [monomialSliceDerivative_positive_formula dimension index point
    selected positive]
  simp only [partialDerivativeCoefficients, restored, exponent]
  ac_rfl

private theorem derivative_term_added_unit {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (source : MultiIndex.carrier dimension) :
    mul (coefficients
      (MultiIndex.addIndex source (MultiIndex.unitIndex selected)))
      (monomialSliceDerivative dimension
        (MultiIndex.addIndex source (MultiIndex.unitIndex selected))
        point selected) =
    mul (partialDerivativeCoefficients selected coefficients source)
      (MultiIndex.monomial dimension source point) := by
  have positive := added_unit_selected_positive selected source
  rw [derivative_term_positive coefficients point selected _ positive]
  have lowered :
      MultiIndex.subIndex
        (MultiIndex.addIndex source (MultiIndex.unitIndex selected))
        (MultiIndex.unitIndex selected) = source := by
    funext coordinate
    simp [MultiIndex.subIndex, MultiIndex.addIndex]
  rw [lowered]

public theorem finite_shell_derivative_eq_partial_shell {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (degreeValue : Nat) :
    finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension (degreeValue + 1))
      point selected =
    shellTerm (partialDerivativeCoefficients selected coefficients)
      point degreeValue := by
  unfold finiteShellSliceDerivative shellTerm
  let summand := fun index : MultiIndex.carrier dimension =>
    mul (coefficients index)
      (monomialSliceDerivative dimension index point selected)
  have filtered := foldr_filter_zero
    (MultiIndex.degreeShell dimension (degreeValue + 1))
    (fun index => decide (0 < index selected)) summand (by
      intro index _ excluded
      apply derivative_term_zero coefficients point selected index
      have nonpositive : ¬ 0 < index selected := by
        intro positive
        have enabled : decide (0 < index selected) = true :=
          decide_eq_true positive
        simp [enabled] at excluded
      omega)
  change _ = _ at filtered
  rw [filtered]
  have permuted := (shell_positive_perm_added_unit
    (degreeValue := degreeValue) selected).foldr_eq'
    (f := fun index total => add (summand index) total)
    (by intro first _ second _ total; ac_rfl) zero
  rw [permuted]
  simp only [List.foldr_map]
  congr 1
  funext index total
  dsimp [summand]
  rw [derivative_term_added_unit]

private theorem monomialSliceBound_eq_derivative_constant
    (dimension : Nat) (index : MultiIndex.carrier dimension)
    (radius : selection.Carrier) (selected : Fin dimension) :
    monomialSliceBound dimension index radius selected =
      monomialSliceDerivative dimension index (fun _ => radius)
        selected := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero => rfl
      | succ selected =>
          change mul (power radius (index 0))
              (monomialSliceBound dimension
                (fun coordinate => index coordinate.succ) radius selected) =
            mul (power radius (index 0))
              (monomialSliceDerivative dimension
                (fun coordinate => index coordinate.succ)
                (fun _ => radius) selected)
          rw [induction]

private theorem derivative_bound_term_zero {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (radius : selection.Carrier) (selected : Fin dimension)
    (index : MultiIndex.carrier dimension)
    (vanished : index selected = 0) :
    mul (abs (coefficients index))
      (monomialSliceBound dimension index radius selected) = zero := by
  have zeroDerivative := monomialSliceDerivative_zero_coordinate_any
    dimension index (fun _ => radius) selected vanished
  rw [monomialSliceBound_eq_derivative_constant,
    zeroDerivative, mul_zero]

private theorem derivative_bound_term_added_unit {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (radius : selection.Carrier) (nonnegative : le zero radius)
    (selected : Fin dimension) (source : MultiIndex.carrier dimension) :
    mul (abs (coefficients
        (MultiIndex.addIndex source (MultiIndex.unitIndex selected))))
      (monomialSliceBound dimension
        (MultiIndex.addIndex source (MultiIndex.unitIndex selected))
        radius selected) =
    abs (mul (partialDerivativeCoefficients selected coefficients source)
      (MultiIndex.monomial dimension source (fun _ => radius))) := by
  have equality := derivative_term_added_unit coefficients
    (fun _ => radius) selected source
  have boundNonnegative := monomialSliceBound_nonnegative dimension
    (MultiIndex.addIndex source (MultiIndex.unitIndex selected))
    nonnegative selected
  rw [← equality, abs_mul]
  rw [← monomialSliceBound_eq_derivative_constant]
  rw [abs_of_nonnegative boundNonnegative]

public theorem finite_shell_derivative_bound_eq_partial_magnitude
    {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (radius : selection.Carrier) (nonnegative : le zero radius)
    (selected : Fin dimension) (degreeValue : Nat) :
    finiteShellSliceBound coefficients
      (MultiIndex.degreeShell dimension (degreeValue + 1))
      radius selected =
    shellMagnitude (partialDerivativeCoefficients selected coefficients)
      (fun _ => radius) degreeValue := by
  unfold finiteShellSliceBound shellMagnitude
  let summand := fun index : MultiIndex.carrier dimension =>
    mul (abs (coefficients index))
      (monomialSliceBound dimension index radius selected)
  have filtered := foldr_filter_zero
    (MultiIndex.degreeShell dimension (degreeValue + 1))
    (fun index => decide (0 < index selected)) summand (by
      intro index _ excluded
      apply derivative_bound_term_zero coefficients radius selected index
      have nonpositive : ¬ 0 < index selected := by
        intro positive
        have enabled : decide (0 < index selected) = true :=
          decide_eq_true positive
        simp [enabled] at excluded
      omega)
  change _ = _ at filtered
  rw [filtered]
  have permuted := (shell_positive_perm_added_unit
    (degreeValue := degreeValue) selected).foldr_eq'
    (f := fun index total => add (summand index) total)
    (by intro first _ second _ total; ac_rfl) zero
  rw [permuted]
  simp only [List.foldr_map]
  congr 1
  funext index total
  dsimp [summand]
  rw [derivative_bound_term_added_unit coefficients radius nonnegative]

/-- Coordinate differentiation yields another convergent power series on a
smaller common-radius ball. The two shrinkages leave a positive majorant
radius inside the original convergence ball. -/
@[expose] public noncomputable def partialDerivativeSeries {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension) :
    Convergent dimension := by
  let ratio := Problib.Analysis.Real.half one
  let outerRadius := Problib.Analysis.Real.half series.radius
  let innerRadius := mul ratio outerRadius
  have ratioPositive := Problib.Analysis.Real.half_positive one_positive
  have outerPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have innerPositive : lt zero innerRadius :=
    mul_positive ratioPositive outerPositive
  have ratioBelowOne : lt ratio one := by
    have raised := add_lt_add_left ratio ratioPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerBelow : lt outerRadius series.radius := by
    have raised := add_lt_add_left outerRadius outerPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => outerRadius) := by
    intro coordinate
    change lt (abs (sub outerRadius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative outerPositive.left]
    exact outerBelow
  refine {
    coefficients := partialDerivativeCoefficients selected series.coefficients
    radius := innerRadius
    radiusPositive := innerPositive
    normalOn := ?_
  }
  intro displacement inside
  let bounds := fun degreeValue => finiteShellSliceBound series.coefficients
    (MultiIndex.degreeShell dimension degreeValue) innerRadius selected
  have boundsSummable : Summable bounds :=
    derivative_shell_bounds_summable series ratioPositive.left
      ratioBelowOne outerPositive outerInside selected
  have boundsNonnegative : ∀ degreeValue, le zero (bounds degreeValue) :=
    fun degreeValue => finiteShellSliceBound_nonnegative
      series.coefficients
      (MultiIndex.degreeShell dimension degreeValue)
      innerPositive.left selected
  have coordinates : ∀ coordinate,
      le (abs (displacement coordinate)) innerRadius := by
    intro coordinate
    have close := inside coordinate
    change lt (abs (sub (displacement coordinate) zero)) innerRadius
      at close
    rw [sub_zero] at close
    exact close.left
  have pointwise : ∀ degreeValue,
      le (tailMagnitudes
        (partialDerivativeCoefficients selected series.coefficients)
        displacement degreeValue)
        (bounds (degreeValue + 2)) := by
    intro degreeValue
    have smaller := shellMagnitude_le_constant
      (partialDerivativeCoefficients selected series.coefficients)
      displacement innerPositive.left coordinates (degreeValue + 1)
    change le _
      (shellMagnitude
        (partialDerivativeCoefficients selected series.coefficients)
        (fun _ => innerRadius) (degreeValue + 1)) at smaller
    rw [← finite_shell_derivative_bound_eq_partial_magnitude
      series.coefficients innerRadius innerPositive.left selected
      (degreeValue + 1)] at smaller
    change le
      (shellMagnitude
        (partialDerivativeCoefficients selected series.coefficients)
        displacement (degreeValue + 1))
      (finiteShellSliceBound series.coefficients
        (MultiIndex.degreeShell dimension (degreeValue + 2))
        innerRadius selected)
    exact smaller
  refine ⟨sum bounds boundsSummable, fun count => ?_⟩
  have pointwiseBound := partial_sum_le pointwise count
  have prefixNonnegative := partial_sum_nonnegative boundsNonnegative 2
  have shiftBound : le (partialSum
      (fun degreeValue => bounds (degreeValue + 2)) count)
      (partialSum bounds (2 + count)) := by
    rw [partial_sum_append bounds 2 count]
    have raised := (add_le_add_right_iff
      (shift := partialSum
        (fun degreeValue => bounds (2 + degreeValue)) count)).mpr
      prefixNonnegative
    simpa only [zero_add, Nat.add_comm] using raised
  exact le_trans pointwiseBound
    (le_trans shiftBound
      (partial_sum_le_sum_nonnegative boundsNonnegative boundsSummable
        (2 + count)))

public theorem derivativeShellValues_zero_any {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    derivativeShellValues series point selected 0 = zero := by
  unfold derivativeShellValues
  rw [MultiIndex.degreeShell_zero_singleton]
  change add
    (mul (series.coefficients (MultiIndex.zeroIndex dimension))
      (monomialSliceDerivative dimension
        (MultiIndex.zeroIndex dimension) point selected)) zero = zero
  rw [monomialSliceDerivative_zero_coordinate_any
    dimension (MultiIndex.zeroIndex dimension) point selected rfl,
    mul_zero, zero_add]

public theorem derivativeShellValues_succ_eq_partial_shell
    {dimension : Nat} (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (degreeValue : Nat) :
    derivativeShellValues series point selected (degreeValue + 1) =
    fullShellTerms (partialDerivativeSeries series selected)
      point degreeValue := by
  exact finite_shell_derivative_eq_partial_shell
    series.coefficients point selected degreeValue

public theorem derivative_shell_sum_eq_partial_series_value
    {dimension : Nat} (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (partialDerivativeSeries series selected).radius point)
    (certificate : Summable (derivativeShellValues series point selected)) :
    sum (derivativeShellValues series point selected) certificate =
    value (partialDerivativeSeries series selected) point inside := by
  let derivative := partialDerivativeSeries series selected
  let original := derivativeShellValues series point selected
  let full := fullShellTerms derivative point
  let fullCertificate := summable_of_absolute_bound
    (fullShellTerms_absolute derivative point inside)
  have shifted : (fun degreeValue => original (degreeValue + 1)) = full := by
    funext degreeValue
    exact derivativeShellValues_succ_eq_partial_shell
      series point selected degreeValue
  have partialSumShift : ∀ count,
      partialSum original (count + 1) = partialSum full count := by
    intro count
    have originalZero : original 0 = zero :=
      derivativeShellValues_zero_any series point selected
    rw [partial_sum_cons, originalZero, shifted, zero_add]
  have shiftedConverges : Problib.Analysis.Real.ConvergesTo
      (fun count => partialSum original (count + 1))
      (sum full fullCertificate) := by
    have equal : (fun count => partialSum original (count + 1)) =
        partialSum full := by
      funext count
      exact partialSumShift count
    rw [equal]
    exact partial_sum_converges full fullCertificate
  have originalConverges : Problib.Analysis.Real.ConvergesTo
      (partialSum original) (sum full fullCertificate) := by
    intro tolerance positive
    rcases shiftedConverges tolerance positive with ⟨stage, close⟩
    refine ⟨stage + 1, fun count later => ?_⟩
    cases count with
    | zero => omega
    | succ count => exact close count (by omega)
  have equal := sum_eq_of_converges original certificate
    originalConverges
  rw [equal]
  exact full_shell_sum_eq_value derivative point inside

public theorem partialDerivativeSeries_radius {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension) :
    (partialDerivativeSeries series selected).radius =
      mul (Problib.Analysis.Real.half one)
        (Problib.Analysis.Real.half series.radius) := rfl

/-- The local analytic value has the formal coefficient derivative at each
point of the shrunken ball, with that derivative evaluated by its own series. -/
public theorem coordinateValueAround_has_derivative_partial_series
    {dimension : Nat} (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (partialDerivativeSeries series selected).radius point) :
    Problib.Analysis.Real.HasDerivative
      (coordinateValueAround series point selected) zero
      (value (partialDerivativeSeries series selected) point inside) := by
  let ratio := Problib.Analysis.Real.half one
  let radius := Problib.Analysis.Real.half series.radius
  have ratioPositive := Problib.Analysis.Real.half_positive one_positive
  have radiusPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have ratioBelowOne : lt ratio one := by
    have raised := add_lt_add_left ratio ratioPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have radiusBelow : lt radius series.radius := by
    have raised := add_lt_add_left radius radiusPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius) := by
    intro coordinate
    change lt (abs (sub radius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative radiusPositive.left]
    exact radiusBelow
  have coordinates : ∀ coordinate,
      lt (abs (point coordinate)) (mul ratio radius) := by
    intro coordinate
    have close := inside coordinate
    rw [partialDerivativeSeries_radius] at close
    change lt (abs (sub (point coordinate) zero))
      (mul ratio radius) at close
    rwa [sub_zero] at close
  have termwise := coordinateValueAround_termwise_derivative series
    ratioPositive ratioBelowOne radiusPositive insideRadius point
    coordinates selected
  have equal := derivative_shell_sum_eq_partial_series_value
    series point selected inside
    (summable_of_absolute_bound
      (derivativeShellValues_absolute series ratioPositive
        ratioBelowOne radiusPositive insideRadius point coordinates
        selected))
  rw [equal] at termwise
  exact termwise

end

end Problib.Analysis.Real.PowerSeries
