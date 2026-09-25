module

public import Problib.Analysis.Real.FiniteVector
public import Problib.Analysis.Real.GeometricSeries

/-! Finite multiindices and their monomials over the sealed real carrier.

The recursive coordinate order agrees with `Fin.cons`: coordinate zero is
removed first. This gives the multivariate series layer a finite degree and a
monomial without importing a polynomial library for another real carrier.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.MultiIndex

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

@[expose] public def carrier (dimension : Nat) : Type := Fin dimension → Nat

@[expose] public def zeroIndex (dimension : Nat) : carrier dimension :=
  fun _ => 0

@[expose] public def addIndex {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => left coordinate + right coordinate

@[expose] public def LeIndex {dimension : Nat}
    (left right : carrier dimension) : Prop :=
  ∀ coordinate, left coordinate ≤ right coordinate

@[expose] public def subIndex {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => left coordinate - right coordinate

@[expose] public def unitIndex {dimension : Nat}
    (selected : Fin dimension) : carrier dimension :=
  fun coordinate => if coordinate = selected then 1 else 0

@[expose] public def degree : (dimension : Nat) → carrier dimension → Nat
  | 0, _ => 0
  | dimension + 1, index =>
      index 0 + degree dimension (fun coordinate => index coordinate.succ)

@[expose] public def monomial : (dimension : Nat) → carrier dimension →
    FiniteVector.carrier dimension → selection.Carrier
  | 0, _, _ => one
  | dimension + 1, index, point =>
      mul (power (point 0) (index 0))
        (monomial dimension
          (fun coordinate => index coordinate.succ)
          (fun coordinate => point coordinate.succ))

public theorem degree_zeroIndex (dimension : Nat) :
    degree dimension (zeroIndex dimension) = 0 := by
  induction dimension with
  | zero => rfl
  | succ dimension induction =>
      change 0 + degree dimension (zeroIndex dimension) = 0
      rw [Nat.zero_add, induction]

public theorem degree_addIndex (dimension : Nat)
    (left right : carrier dimension) :
    degree dimension (addIndex left right) =
      degree dimension left + degree dimension right := by
  induction dimension with
  | zero => rfl
  | succ dimension induction =>
      change (left 0 + right 0) +
          degree dimension (addIndex
            (fun coordinate => left coordinate.succ)
            (fun coordinate => right coordinate.succ)) =
        (left 0 + degree dimension (fun coordinate => left coordinate.succ)) +
          (right 0 + degree dimension (fun coordinate => right coordinate.succ))
      rw [induction]
      omega

public theorem degree_mono (dimension : Nat)
    {left right : carrier dimension} (included : LeIndex left right) :
    degree dimension left ≤ degree dimension right := by
  induction dimension with
  | zero => exact Nat.le_refl _
  | succ dimension induction =>
      change left 0 + degree dimension
          (fun coordinate => left coordinate.succ) ≤
        right 0 + degree dimension
          (fun coordinate => right coordinate.succ)
      exact Nat.add_le_add (included 0)
        (induction (fun coordinate => included coordinate.succ))

public theorem add_subIndex {dimension : Nat}
    {left right : carrier dimension} (included : LeIndex right left) :
    addIndex right (subIndex left right) = left := by
  funext coordinate
  exact Nat.add_sub_of_le (included coordinate)

public theorem degree_subIndex {dimension : Nat}
    {left right : carrier dimension} (included : LeIndex right left) :
    degree dimension (subIndex left right) =
      degree dimension left - degree dimension right := by
  have equal := congrArg (degree dimension) (add_subIndex included)
  rw [degree_addIndex] at equal
  omega

/-- Every coordinate contributes at most the total degree. -/
public theorem coordinate_le_degree (dimension : Nat)
    (index : carrier dimension) (coordinate : Fin dimension) :
    index coordinate ≤ degree dimension index := by
  induction dimension with
  | zero => exact coordinate.elim0
  | succ dimension induction =>
      cases coordinate using Fin.cases with
      | zero =>
          change index 0 ≤ index 0 +
            degree dimension (fun coordinate => index coordinate.succ)
          exact Nat.le_add_right _ _
      | succ coordinate =>
          change index coordinate.succ ≤ index 0 +
            degree dimension (fun coordinate => index coordinate.succ)
          exact Nat.le_trans
            (induction (fun coordinate => index coordinate.succ) coordinate)
            (Nat.le_add_left _ _)

public theorem eq_zeroIndex_of_degree_zero (dimension : Nat)
    (index : carrier dimension)
    (vanished : degree dimension index = 0) :
    index = zeroIndex dimension := by
  funext coordinate
  have included := coordinate_le_degree dimension index coordinate
  rw [vanished] at included
  change index coordinate = 0
  omega

public theorem degree_unitIndex (dimension : Nat)
    (selected : Fin dimension) :
    degree dimension (unitIndex selected) = 1 := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          have tailZero :
              (fun coordinate : Fin dimension =>
                unitIndex (0 : Fin (dimension + 1)) coordinate.succ) =
              zeroIndex dimension := by
            funext coordinate
            have distinct : coordinate.succ ≠
                (0 : Fin (dimension + 1)) := Fin.succ_ne_zero coordinate
            simp [unitIndex, zeroIndex, distinct]
          change unitIndex (0 : Fin (dimension + 1)) 0 +
              degree dimension
                (fun coordinate =>
                  unitIndex (0 : Fin (dimension + 1)) coordinate.succ) = 1
          rw [tailZero, degree_zeroIndex]
          simp [unitIndex]
      | succ selected =>
          have tailUnit :
              (fun coordinate : Fin dimension =>
                unitIndex selected.succ coordinate.succ) =
              unitIndex selected := by
            funext coordinate
            simp [unitIndex]
          change unitIndex selected.succ 0 +
              degree dimension
                (fun coordinate => unitIndex selected.succ coordinate.succ) = 1
          rw [tailUnit, induction]
          have distinct : (0 : Fin (dimension + 1)) ≠ selected.succ :=
            fun equal => Fin.succ_ne_zero selected equal.symm
          simp [unitIndex, distinct]

/-- All multiindices whose coordinates are at most `bound`. -/
@[expose] public def boundedIndices : (dimension bound : Nat) →
    List (carrier dimension)
  | 0, _ => [fun coordinate => coordinate.elim0]
  | dimension + 1, bound =>
      (List.range (bound + 1)).flatMap fun head =>
        (boundedIndices dimension bound).map fun tail => Fin.cases head tail

/-- The finite shell of multiindices of a fixed total degree. -/
@[expose] public noncomputable def degreeShell (dimension degreeValue : Nat) :
    List (carrier dimension) :=
  (boundedIndices dimension degreeValue).filter
    (fun index => degree dimension index = degreeValue)

/-- The finite set of candidate left factors of a multiindex. -/
@[expose] public noncomputable def splitIndices {dimension : Nat}
    (index : carrier dimension) : List (carrier dimension) := by
  classical
  exact (boundedIndices dimension (degree dimension index)).filter
    (fun left => LeIndex left index)

public theorem mem_boundedIndices (dimension bound : Nat)
    (index : carrier dimension)
    (bounded : ∀ coordinate, index coordinate ≤ bound) :
    index ∈ boundedIndices dimension bound := by
  induction dimension with
  | zero =>
      have unique : index = (fun coordinate => coordinate.elim0) := by
        funext coordinate
        exact coordinate.elim0
      rw [unique]
      simp only [boundedIndices, List.mem_singleton]
  | succ dimension induction =>
      have headMember : index 0 ∈ List.range (bound + 1) :=
        List.mem_range.mpr (Nat.lt_succ_of_le (bounded 0))
      have tailMember :
          (fun coordinate => index coordinate.succ) ∈
            boundedIndices dimension bound :=
        induction (fun coordinate => index coordinate.succ)
          (fun coordinate => bounded coordinate.succ)
      have eta :
          (Fin.cases (index 0)
            (fun coordinate => index coordinate.succ)) = index := by
        funext coordinate
        cases coordinate using Fin.cases <;> rfl
      simp only [boundedIndices, List.mem_flatMap, List.mem_map]
      exact ⟨index 0, headMember,
        ⟨(fun coordinate => index coordinate.succ), tailMember, eta⟩⟩

public theorem boundedIndices_nodup (dimension bound : Nat) :
    (boundedIndices dimension bound).Nodup := by
  induction dimension with
  | zero => simp [boundedIndices]
  | succ dimension induction =>
      simp only [boundedIndices]
      apply (List.pairwise_flatMap).mpr
      constructor
      · intro head _
        apply (List.pairwise_map).mpr
        apply induction.imp
        intro left right distinct same
        apply distinct
        funext coordinate
        exact congrFun same coordinate.succ
      · apply (List.nodup_range).imp
        intro first second distinct left leftMember right rightMember same
        apply distinct
        have firstHead : left 0 = first := by
          rcases List.mem_map.mp leftMember with ⟨tail, _, equal⟩
          rw [← equal]
          rfl
        have secondHead : right 0 = second := by
          rcases List.mem_map.mp rightMember with ⟨tail, _, equal⟩
          rw [← equal]
          rfl
        rw [← firstHead, ← secondHead]
        exact congrFun same 0

public theorem degreeShell_nodup (dimension degreeValue : Nat) :
    (degreeShell dimension degreeValue).Nodup := by
  unfold degreeShell
  exact (boundedIndices_nodup dimension degreeValue).filter _

public theorem mem_degreeShell (dimension : Nat)
    (index : carrier dimension) :
    index ∈ degreeShell dimension (degree dimension index) := by
  apply List.mem_filter.mpr
  exact ⟨mem_boundedIndices dimension (degree dimension index) index
    (coordinate_le_degree dimension index), by simp⟩

public theorem degree_of_mem_shell {dimension degreeValue : Nat}
    {index : carrier dimension}
    (member : index ∈ degreeShell dimension degreeValue) :
    degree dimension index = degreeValue := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

public theorem mem_degreeShell_iff {dimension degreeValue : Nat}
    {index : carrier dimension} :
    index ∈ degreeShell dimension degreeValue ↔
      degree dimension index = degreeValue := by
  constructor
  · exact degree_of_mem_shell
  · intro equal
    subst degreeValue
    exact mem_degreeShell dimension index

public theorem degreeShell_zero_singleton (dimension : Nat) :
    degreeShell dimension 0 = [zeroIndex dimension] := by
  have nonempty : zeroIndex dimension ∈ degreeShell dimension 0 := by
    apply (mem_degreeShell_iff).mpr
    exact degree_zeroIndex dimension
  have unique : ∀ index, index ∈ degreeShell dimension 0 →
      index = zeroIndex dimension := by
    intro index member
    exact eq_zeroIndex_of_degree_zero dimension index
      (degree_of_mem_shell member)
  have nodup : (degreeShell dimension 0).Nodup :=
    degreeShell_nodup dimension 0
  cases equal : degreeShell dimension 0 with
  | nil =>
      rw [equal] at nonempty
      exact False.elim (List.not_mem_nil nonempty)
  | cons head tail =>
      have headEqual : head = zeroIndex dimension :=
        unique head (by rw [equal]; exact List.mem_cons_self)
      subst head
      rw [equal] at nodup
      cases tail with
      | nil => rfl
      | cons next rest =>
          have nextEqual : next = zeroIndex dimension :=
            unique next (by
              rw [equal]
              exact List.mem_cons_of_mem _ List.mem_cons_self)
          subst next
          exact False.elim
            ((List.nodup_cons.mp nodup).left List.mem_cons_self)

public theorem mem_splitIndices_iff {dimension : Nat}
    {index left : carrier dimension} :
    left ∈ splitIndices index ↔ LeIndex left index := by
  classical
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).right
  · intro included
    apply List.mem_filter.mpr
    refine ⟨mem_boundedIndices dimension (degree dimension index) left
      (fun coordinate => Nat.le_trans (included coordinate)
        (coordinate_le_degree dimension index coordinate)), ?_⟩
    simp [included]

public theorem splitIndices_nodup {dimension : Nat}
    (index : carrier dimension) :
    (splitIndices index).Nodup := by
  unfold splitIndices
  exact (boundedIndices_nodup dimension (degree dimension index)).filter _

public theorem monomial_zeroIndex (dimension : Nat)
    (point : FiniteVector.carrier dimension) :
    monomial dimension (zeroIndex dimension) point = one := by
  induction dimension with
  | zero => rfl
  | succ dimension induction =>
      change mul (power (point 0) 0)
        (monomial dimension (zeroIndex dimension)
          (fun coordinate => point coordinate.succ)) = one
      rw [power_zero, one_mul]
      exact induction (fun coordinate => point coordinate.succ)

public theorem monomial_unitIndex (dimension : Nat)
    (selected : Fin dimension)
    (point : FiniteVector.carrier dimension) :
    monomial dimension (unitIndex selected) point = point selected := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          have tailZero :
              (fun coordinate : Fin dimension =>
                unitIndex (0 : Fin (dimension + 1)) coordinate.succ) =
              zeroIndex dimension := by
            funext coordinate
            have distinct : coordinate.succ ≠
                (0 : Fin (dimension + 1)) := Fin.succ_ne_zero coordinate
            simp [unitIndex, zeroIndex, distinct]
          change mul
            (power (point 0) (unitIndex (0 : Fin (dimension + 1)) 0))
            (monomial dimension
              (fun coordinate =>
                unitIndex (0 : Fin (dimension + 1)) coordinate.succ)
              (fun coordinate => point coordinate.succ)) = point 0
          rw [tailZero, monomial_zeroIndex]
          simp [unitIndex, power_succ, power_zero, mul_one]
      | succ selected =>
          have tailUnit :
              (fun coordinate : Fin dimension =>
                unitIndex selected.succ coordinate.succ) =
              unitIndex selected := by
            funext coordinate
            simp [unitIndex]
          change mul (power (point 0) (unitIndex selected.succ 0))
            (monomial dimension
              (fun coordinate => unitIndex selected.succ coordinate.succ)
              (fun coordinate => point coordinate.succ)) =
            point selected.succ
          rw [tailUnit, induction]
          have distinct : (0 : Fin (dimension + 1)) ≠ selected.succ :=
            fun equal => Fin.succ_ne_zero selected equal.symm
          simp [unitIndex, distinct, power_zero, one_mul]

/-- Exponent addition becomes multiplication of monomials. -/
public theorem monomial_addIndex (dimension : Nat)
    (left right : carrier dimension)
    (point : FiniteVector.carrier dimension) :
    monomial dimension (addIndex left right) point =
      mul (monomial dimension left point)
        (monomial dimension right point) := by
  induction dimension with
  | zero =>
      change one = mul one one
      rw [one_mul]
  | succ dimension induction =>
      change mul (power (point 0) (left 0 + right 0))
          (monomial dimension
            (addIndex (fun coordinate => left coordinate.succ)
              (fun coordinate => right coordinate.succ))
            (fun coordinate => point coordinate.succ)) =
        mul (mul (power (point 0) (left 0))
          (monomial dimension (fun coordinate => left coordinate.succ)
            (fun coordinate => point coordinate.succ)))
          (mul (power (point 0) (right 0))
            (monomial dimension (fun coordinate => right coordinate.succ)
              (fun coordinate => point coordinate.succ)))
      rw [power_add, induction]
      ac_rfl

public theorem power_mono_base {small large : selection.Carrier}
    (smallNonnegative : le zero small) (included : le small large)
    (count : Nat) : le (power small count) (power large count) := by
  have largeNonnegative := le_trans smallNonnegative included
  induction count with
  | zero => exact le_refl one
  | succ count induction =>
      rw [power_succ, power_succ]
      exact le_trans
        (mul_le_mul_nonnegative_right included
          (power_nonnegative smallNonnegative count))
        (mul_le_mul_nonnegative_left induction largeNonnegative)

public theorem abs_monomial (dimension : Nat)
    (index : carrier dimension)
    (point : FiniteVector.carrier dimension) :
    abs (monomial dimension index point) =
      monomial dimension index (fun coordinate => abs (point coordinate)) := by
  induction dimension with
  | zero =>
      change abs one = one
      exact abs_of_nonnegative one_nonnegative
  | succ dimension induction =>
      change abs (mul (power (point 0) (index 0))
          (monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ))) =
        mul (power (abs (point 0)) (index 0))
          (monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => abs (point coordinate.succ)))
      rw [abs_mul, abs_power, induction]

/-- A common bound on coordinate magnitudes bounds every monomial by the
corresponding power of the total degree. -/
public theorem abs_monomial_le_power (dimension : Nat)
    (index : carrier dimension)
    (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (point coordinate)) radius) :
    le (abs (monomial dimension index point))
      (power radius (degree dimension index)) := by
  induction dimension with
  | zero =>
      change le (abs one) one
      rw [abs_of_nonnegative one_nonnegative]
      exact le_refl one
  | succ dimension induction =>
      rw [abs_monomial]
      change le
        (mul (power (abs (point 0)) (index 0))
          (monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => abs (point coordinate.succ))))
        (power radius
          (index 0 + degree dimension
            (fun coordinate => index coordinate.succ)))
      rw [power_add]
      have headBound := power_mono_base
        (abs_nonnegative (point 0)) (coordinates 0) (index 0)
      have tailBound := induction
        (fun coordinate => index coordinate.succ)
        (fun coordinate => point coordinate.succ)
        (fun coordinate => coordinates coordinate.succ)
      rw [abs_monomial] at tailBound
      exact le_trans
        (mul_le_mul_nonnegative_right headBound
          (by
            rw [← abs_monomial]
            exact abs_nonnegative _))
        (mul_le_mul_nonnegative_left tailBound
          (power_nonnegative nonnegative (index 0)))

public theorem monomial_constant_radius (dimension : Nat)
    (index : carrier dimension) (radius : selection.Carrier) :
    monomial dimension index (fun _ => radius) =
      power radius (degree dimension index) := by
  induction dimension with
  | zero => rfl
  | succ dimension induction =>
      change mul (power radius (index 0))
          (monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun _ => radius)) =
        power radius
          (index 0 + degree dimension
            (fun coordinate => index coordinate.succ))
      rw [induction, power_add]

public theorem monomial_zero_of_positive_degree (dimension : Nat)
    (index : carrier dimension)
    (positive : 0 < degree dimension index) :
    monomial dimension index (FiniteVector.zeroVector dimension) = zero := by
  induction dimension with
  | zero =>
      have impossible : ¬0 < 0 := Nat.lt_irrefl 0
      exact (impossible positive).elim
  | succ dimension induction =>
      let tailIndex : carrier dimension :=
        fun coordinate => index coordinate.succ
      change mul (power zero (index 0))
        (monomial dimension tailIndex
          (FiniteVector.zeroVector dimension)) = zero
      cases head : index 0 with
      | zero =>
          have tailPositive : 0 < degree dimension tailIndex := by
            change 0 < index 0 + degree dimension tailIndex at positive
            omega
          rw [power_zero, one_mul]
          exact induction tailIndex tailPositive
      | succ count =>
          rw [power_succ, zero_mul, zero_mul]

public theorem eq_unitIndex_of_degree_one_at_coordinate
    (dimension : Nat) (index : carrier dimension)
    (selected : Fin dimension)
    (degreeOne : degree dimension index = 1)
    (coordinateOne : index selected = 1) :
    index = unitIndex selected := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      let tailIndex : carrier dimension :=
        fun coordinate => index coordinate.succ
      cases selected using Fin.cases with
      | zero =>
          have tailZero : degree dimension tailIndex = 0 := by
            change index 0 + degree dimension tailIndex = 1 at degreeOne
            omega
          have tailEqual := eq_zeroIndex_of_degree_zero dimension
            tailIndex tailZero
          funext coordinate
          cases coordinate using Fin.cases with
          | zero =>
              simpa [unitIndex] using coordinateOne
          | succ coordinate =>
              have zeroValue := congrFun tailEqual coordinate
              simpa [tailIndex, zeroIndex, unitIndex,
                Fin.succ_ne_zero coordinate] using zeroValue
      | succ selected =>
          have tailAtOne : tailIndex selected = 1 := coordinateOne
          have tailAtMost : tailIndex selected ≤ degree dimension tailIndex :=
            coordinate_le_degree dimension tailIndex selected
          have headZero : index 0 = 0 := by
            change index 0 + degree dimension tailIndex = 1 at degreeOne
            omega
          have tailOne : degree dimension tailIndex = 1 := by
            change index 0 + degree dimension tailIndex = 1 at degreeOne
            omega
          have tailEqual := induction tailIndex selected tailOne tailAtOne
          funext coordinate
          cases coordinate using Fin.cases with
          | zero =>
              have distinct : (0 : Fin (dimension + 1)) ≠
                  selected.succ :=
                fun equal => Fin.succ_ne_zero selected equal.symm
              simpa [unitIndex, distinct] using headZero
          | succ coordinate =>
              have equal := congrFun tailEqual coordinate
              simpa [tailIndex, unitIndex] using equal

end

end Problib.Analysis.Real.MultiIndex
