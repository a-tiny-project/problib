module

public import Problib.Measure.Equivalence.Fibred
public import Problib.Measure.Configuration.Reference

set_option autoImplicit false

/-!
# Schedule lenses

A removal schedule takes entries out of a list one position at a time
(`removeAll`). The schedule lens pairs a list with what remains and what was
removed, and reinserts the removed entries along the reversed schedule. On
the configuration reference with coefficients `c`, removing `k` entries from
a list of length `n = m + k` changes reference by `c(m + k) / c(m)`, read at
the remaining length `m` (`scheduleLens_reference_change`). The removed
entries carry the ordered iid power of length `k`.

The front lens brings one position of a list to the front, beside the rest
(`frontLens`). On an ordered iid power it preserves reference: the entry and
the rest are independent, with the entry's law and the shorter power
(`frontLens_reference_change`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (ofReal_measurable)
open Problib.Measure.ListSpace (coordinate)

universe u

variable {α : Type u} {element : Space α}

public section

/-- A valid removal schedule is no longer than the list it removes from. -/
theorem valid_removal_length {positions : List Nat} {length : Nat}
    (valid : ValidRemoval positions length) : positions.length ≤ length := by
  induction positions generalizing length with
  | nil => exact Nat.zero_le _
  | cons index rest induction =>
      have tail := induction valid.2
      have below := valid.1
      simp only [List.length_cons]
      omega

/-- A valid insertion adds one entry per position. -/
theorem insertAll_length {positions : List Nat} {inserted values : List α}
    (valid : ValidInsertion positions values.length)
    (same : inserted.length = positions.length) :
    (insertAll positions inserted values).length = values.length + positions.length := by
  induction positions generalizing inserted values with
  | nil =>
      cases inserted with
      | nil => simp [insertAll]
      | cons head tail => cases same
  | cons index rest induction =>
      cases inserted with
      | nil => cases same
      | cons value remainder =>
          have included := valid.1
          have tailValid : ValidInsertion rest (values.insertIdx index value).length := by
            simpa only [List.length_insertIdx_of_le_length included value] using valid.2
          have step := induction (inserted := remainder) (values := values.insertIdx index value)
            tailValid (Nat.succ.inj same)
          simp only [insertAll]
          rw [step, List.length_insertIdx_of_le_length included value, List.length_cons]
          omega

/-- Remove the entries at a schedule, keeping the rest and the removed entries
in removal order. The inverse reinserts them along the reversed schedule. -/
@[expose] def scheduleLens (element : Space α) (positions : List Nat) :
    MeasurablePartialEquivalence (Space.list element)
      (Space.product (Space.list element) (Space.list element)) where
  forward := removeAll positions
  inverse := fun pair => insertAll positions.reverse pair.2.reverse pair.1
  sourceDomain := fun values => ValidRemoval positions values.length
  targetDomain := fun pair =>
    ValidRemoval positions (pair.1.length + positions.length) ∧
      pair.2.length = positions.length
  sourceMeasurable := ListSpace.length_measurable element
    (set := fun length => ValidRemoval positions length) trivial
  targetMeasurable := (Space.product (Space.list element) (Space.list element)).inter
    (Space.first_measurable _ _ (ListSpace.length_measurable element
      (set := fun length => ValidRemoval positions (length + positions.length)) trivial))
    (Space.second_measurable _ _ (ListSpace.length_measurable element
      (set := fun length => length = positions.length) trivial))
  forward_mem := by
    intro values valid
    have lengths := removeAll_length valid
    have enough := valid_removal_length valid
    refine ⟨?_, lengths.2⟩
    rw [lengths.1, Nat.sub_add_cancel enough]
    exact valid
  inverse_mem := by
    rintro ⟨rest, removed⟩ ⟨valid, same⟩
    have insertion := valid_insertion_reverse valid
    change ValidRemoval positions (insertAll positions.reverse removed.reverse rest).length
    rw [insertAll_length insertion (by rw [List.length_reverse, List.length_reverse, same]),
      List.length_reverse]
    exact valid
  inverse_forward := fun _ valid => insertAll_removeAll valid
  forward_inverse := by
    rintro ⟨rest, removed⟩ ⟨valid, same⟩
    have insertion := valid_insertion_reverse valid
    have restored := removeAll_insertAll (inserted := removed.reverse) insertion
      (by rw [List.length_reverse, List.length_reverse, same])
    simp only [List.reverse_reverse] at restored
    exact restored
  forwardMeasurable := removeAll_at_measurable element positions
  inverseMeasurable := MeasurableMap.comp (insertAll_at_measurable element positions.reverse)
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (reverse_measurable element) (Space.second_measurable _ _)))

private theorem indicator_apply {β : Type u} (region : Set β) (function : β → ENNReal)
    (point : β) [Decidable (region point)] :
    ennrealIndicator region function point =
      if region point then function point else ENNReal.zero := by
  unfold ennrealIndicator ennrealPiecewise
  by_cases member : region point
  · rw [ite_eq_left member, ite_eq_left member]
  · rw [ite_eq_right member, ite_eq_right member]

/-- A series whose first `shift` terms vanish is the series of its later terms. -/
private theorem tsum_shift (values : Nat → ENNReal) (shift : Nat)
    (vanish : ∀ index, index < shift → values index = ENNReal.zero) :
    ENNReal.tsum values = ENNReal.tsum (fun index => values (index + shift)) := by
  have spread : ∀ index, values index = ENNReal.tsum (fun other =>
      if index = other + shift then values index else ENNReal.zero) := by
    intro index
    by_cases large : shift ≤ index
    · rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ (index - shift)]
      · rw [ite_eq_left (by omega)]
      · intro other different
        rw [ite_eq_right (by omega)]
    · rw [vanish index (by omega)]
      symm
      apply ENNReal.tsum_eq_zero_iff.mpr
      intro other
      split <;> rfl
  calc
    ENNReal.tsum values = ENNReal.tsum (fun index => ENNReal.tsum (fun other =>
        if index = other + shift then values index else ENNReal.zero)) :=
      ENNReal.tsum_congr spread
    _ = ENNReal.tsum (fun other => ENNReal.tsum (fun index =>
        if index = other + shift then values index else ENNReal.zero)) :=
      ENNReal.tsum_comm (fun index other =>
        if index = other + shift then values index else ENNReal.zero)
    _ = ENNReal.tsum (fun other => values (other + shift)) := by
      apply ENNReal.tsum_congr
      intro other
      rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ (other + shift)]
      · rw [ite_eq_left rfl]
      · intro index different
        rw [ite_eq_right different]

/-- Removing along a schedule of `k` positions changes the configuration
reference by `c(m + k) / c(m)` at remaining length `m`, with the removed
entries under the ordered iid power of length `k`. -/
theorem scheduleLens_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) {coefficient : Nat → NNReal}
    (nonzero : ∀ count, coefficient count ≠ NNReal.zero) (positions : List Nat) :
    (scheduleLens element positions).ReferenceChange
      (configurationReference reference finite coefficient)
      (Measure.prod (configurationReference reference finite coefficient)
        (Measure.listPower reference finite positions.length)
        (Measure.SFinite.listPower finite positions.length))
      (fun pair =>
        NNReal.toReal (coefficientRatio coefficient positions.length 0 pair.1.length)) := by
  classical
  have unitRatio : ∀ value : NNReal,
      ENNReal.ofReal (NNReal.toReal value) = ENNReal.finite value :=
    fun value => ENNReal.ofReal_toReal_finite value
  have lengthAE : ∀ count, (Measure.listPower reference finite count).AE
      (fun values : List α => values.length = count) := fun count =>
    Measure.NullSet.mono (Measure.listPower_length_null reference finite count)
      (fun {_} failure => failure)
  have weightMeasurable : ENNRealMeasurable
      (Space.product (Space.list element) (Space.list element))
      (fun pair : List α × List α => ENNReal.ofReal
        (NNReal.toReal (coefficientRatio coefficient positions.length 0 pair.1.length))) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (MeasurableMap.comp
        (MeasurableMap.from_discrete Real.borel (fun length =>
          NNReal.toReal (coefficientRatio coefficient positions.length 0 length)))
        (MeasurableMap.comp (ListSpace.length_measurable element)
          (Space.first_measurable _ _)))
  unfold MeasurablePartialEquivalence.ReferenceChange
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  have sliceMeasurable : ∀ values : List α,
      ENNRealMeasurable (Space.list element) (fun removed => function (values, removed)) :=
    fun values => ENNRealMeasurable.comp functionMeasurable
      (Kernel.pair_left_measurable (source := Space.list element)
        (target := Space.list element) values)
  have innerMeasurable : ENNRealMeasurable (Space.list element) (fun values =>
      lintegral (Measure.listPower reference finite positions.length)
        (fun removed => function (values, removed))) :=
    Kernel.lintegral_measurable_joint
      (Kernel.const _ (Measure.listPower reference finite positions.length))
      (Kernel.IsSFinite.const _ (Measure.SFinite.listPower finite positions.length))
      (function := fun values removed => function (values, removed)) functionMeasurable
  have leftSide : lintegral
      (((configurationReference reference finite coefficient).restrict
        (scheduleLens element positions).sourceDomain).map
        (scheduleLens element positions).forward
        (scheduleLens element positions).forwardMeasurable) function =
      ENNReal.tsum (fun length => ENNReal.mul (ENNReal.finite (coefficient length))
        (if ValidRemoval positions length then
          lintegral (Measure.prod (Measure.listPower reference finite (length - positions.length))
            (Measure.listPower reference finite positions.length)
            (Measure.SFinite.listPower finite positions.length)) function
        else ENNReal.zero)) := by
    rw [lintegral_map _ _ _ functionMeasurable,
      ← lintegral_indicator _ _ (scheduleLens element positions).sourceMeasurable,
      configurationReference, lintegral_sum]
    apply ENNReal.tsum_congr
    intro length
    rw [lintegral_smul_measure]
    congr 1
    by_cases valid : ValidRemoval positions length
    · rw [ite_eq_left valid]
      obtain ⟨rest, rfl⟩ : ∃ rest, length = rest + positions.length :=
        ⟨length - positions.length, (Nat.sub_add_cancel (valid_removal_length valid)).symm⟩
      rw [Nat.add_sub_cancel]
      have almost : (Measure.listPower reference finite (rest + positions.length)).AEEq
          (ennrealIndicator (scheduleLens element positions).sourceDomain
            (fun values => function ((scheduleLens element positions).forward values)))
          (fun values => function (removeAll positions values)) := by
        refine (lengthAE (rest + positions.length)).mono ?_
        intro values same
        have inside : (scheduleLens element positions).sourceDomain values := by
          change ValidRemoval positions values.length
          rw [same]
          exact valid
        rw [indicator_apply, ite_eq_left inside]
        rfl
      rw [lintegral_congr_ae almost,
        ← lintegral_map _ (removeAll positions) (removeAll_at_measurable element positions)
          functionMeasurable,
        Measure.removeAll_power reference finite valid]
    · rw [ite_eq_right valid]
      have almost : (Measure.listPower reference finite length).AEEq
          (ennrealIndicator (scheduleLens element positions).sourceDomain
            (fun values => function ((scheduleLens element positions).forward values)))
          (fun _ => ENNReal.zero) := by
        refine (lengthAE length).mono ?_
        intro values same
        have outside : ¬ (scheduleLens element positions).sourceDomain values := by
          change ¬ ValidRemoval positions values.length
          rw [same]
          exact valid
        rw [indicator_apply, ite_eq_right outside]
      exact (lintegral_congr_ae almost).trans (lintegral_zero _)
  have rightSide : lintegral
      (((Measure.prod (configurationReference reference finite coefficient)
          (Measure.listPower reference finite positions.length)
          (Measure.SFinite.listPower finite positions.length)).restrict
        (scheduleLens element positions).targetDomain).withDensity
        (fun pair => ENNReal.ofReal
          (NNReal.toReal (coefficientRatio coefficient positions.length 0 pair.1.length))))
        function =
      ENNReal.tsum (fun rest => ENNReal.mul (ENNReal.finite (coefficient rest))
        (if ValidRemoval positions (rest + positions.length) then
          ENNReal.mul
            (ENNReal.finite (coefficientRatio coefficient positions.length 0 rest))
            (lintegral (Measure.prod (Measure.listPower reference finite rest)
              (Measure.listPower reference finite positions.length)
              (Measure.SFinite.listPower finite positions.length)) function)
        else ENNReal.zero)) := by
    rw [lintegral_withDensity _ weightMeasurable functionMeasurable,
      ← lintegral_indicator _ _ (scheduleLens element positions).targetMeasurable,
      lintegral_prod _ _ _ (ENNRealMeasurable.indicator
        (scheduleLens element positions).targetMeasurable
        (ENNRealMeasurable.mul weightMeasurable functionMeasurable)),
      configurationReference, lintegral_sum]
    apply ENNReal.tsum_congr
    intro rest
    rw [lintegral_smul_measure]
    congr 1
    by_cases valid : ValidRemoval positions (rest + positions.length)
    · rw [ite_eq_left valid, lintegral_prod _ _ _ functionMeasurable,
        ← lintegral_smul _ _ innerMeasurable]
      apply lintegral_congr_ae
      refine (lengthAE rest).mono ?_
      intro values same
      dsimp only
      rw [← lintegral_smul _ _ (sliceMeasurable values)]
      apply lintegral_congr_ae
      refine (lengthAE positions.length).mono ?_
      intro removed removedSame
      dsimp only
      have inside : (scheduleLens element positions).targetDomain (values, removed) := by
        refine ⟨?_, removedSame⟩
        change ValidRemoval positions (values.length + positions.length)
        rw [same]
        exact valid
      rw [indicator_apply, ite_eq_left inside]
      change ENNReal.mul (ENNReal.ofReal (NNReal.toReal
          (coefficientRatio coefficient positions.length 0 values.length)))
          (function (values, removed)) = _
      rw [same, unitRatio]
    · rw [ite_eq_right valid]
      have almost : (Measure.listPower reference finite rest).AEEq
          (fun values => lintegral (Measure.listPower reference finite positions.length)
            (fun removed => ennrealIndicator (scheduleLens element positions).targetDomain
              (fun pair => ENNReal.mul (ENNReal.ofReal (NNReal.toReal
                (coefficientRatio coefficient positions.length 0 pair.1.length)))
                (function pair)) (values, removed)))
          (fun _ => ENNReal.zero) := by
        refine (lengthAE rest).mono ?_
        intro values same
        refine (lintegral_congr _ (fun removed => ?_)).trans (lintegral_zero _)
        rw [indicator_apply, ite_eq_right (fun inside => valid (by rw [← same]; exact inside.1))]
      exact (lintegral_congr_ae almost).trans (lintegral_zero _)
  rw [leftSide, rightSide, tsum_shift _ positions.length]
  · apply ENNReal.tsum_congr
    intro rest
    rw [Nat.add_sub_cancel]
    by_cases valid : ValidRemoval positions (rest + positions.length)
    · rw [ite_eq_left valid, ite_eq_left valid, ← ENNReal.mul_assoc, ENNReal.finite_mul_finite]
      unfold coefficientRatio
      rw [Nat.sub_zero, NNReal.mul_div_cancel _ (nonzero rest)]
    · rw [ite_eq_right valid, ite_eq_right valid, ENNReal.mul_zero, ENNReal.mul_zero]
  · intro length short
    rw [ite_eq_right (fun valid => absurd (valid_removal_length valid) (by omega)),
      ENNReal.mul_zero]

private theorem coordinate_of_lt {values : List α} {index : Nat}
    (below : index < values.length) :
    coordinate index values = Sum.inr values[index] := by
  induction values generalizing index with
  | nil => exact absurd below (Nat.not_lt_zero _)
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index => exact induction (Nat.lt_of_succ_lt_succ below)

private theorem coordinate_insertIdx {rest : List α} {index : Nat} (value : α)
    (within : index ≤ rest.length) :
    coordinate index (rest.insertIdx index value) = Sum.inr value := by
  induction rest generalizing index with
  | nil =>
      have zero : index = 0 := Nat.le_zero.mp within
      subst zero
      rfl
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          rw [List.insertIdx_succ_cons]
          exact induction (Nat.le_of_succ_le_succ within)

private theorem eraseIdx_insertIdx {rest : List α} {index : Nat} (value : α)
    (within : index ≤ rest.length) :
    (rest.insertIdx index value).eraseIdx index = rest := by
  induction rest generalizing index with
  | nil =>
      have zero : index = 0 := Nat.le_zero.mp within
      subst zero
      rfl
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          rw [List.insertIdx_succ_cons, List.eraseIdx_cons_succ,
            induction (Nat.le_of_succ_le_succ within)]

/-- Position `index` of a list, brought to the front beside the rest. The
domain is the lists long enough to have the position. Outside it the front
entry is the fallback, which no reference change sees. -/
@[expose] def frontLens (element : Space α) (fallback : α) (index : Nat) :
    MeasurablePartialEquivalence (Space.list element)
      (Space.product element (Space.list element)) where
  forward := fun values =>
    (Sum.elim (fun _ => fallback) (fun value => value) (coordinate index values),
      values.eraseIdx index)
  inverse := fun pair => pair.2.insertIdx index pair.1
  sourceDomain := fun values => index < values.length
  targetDomain := fun pair => index ≤ pair.2.length
  sourceMeasurable :=
    ListSpace.length_measurable element (set := fun length => index < length) trivial
  targetMeasurable := Space.second_measurable element (Space.list element)
    (ListSpace.length_measurable element (set := fun length => index ≤ length) trivial)
  forward_mem := fun values below => by
    change index ≤ (values.eraseIdx index).length
    rw [List.length_eraseIdx_of_lt below]
    omega
  inverse_mem := fun pair within => by
    change index < (pair.2.insertIdx index pair.1).length
    rw [List.length_insertIdx_of_le_length within pair.1]
    omega
  inverse_forward := fun values below => by
    change (values.eraseIdx index).insertIdx index
      (Sum.elim (fun _ => fallback) (fun value => value) (coordinate index values)) = values
    rw [coordinate_of_lt below]
    exact insertIdx_eraseIdx_self below
  forward_inverse := fun pair within => by
    change (Sum.elim (fun _ => fallback) (fun value => value)
        (coordinate index (pair.2.insertIdx index pair.1)),
      (pair.2.insertIdx index pair.1).eraseIdx index) = pair
    rw [coordinate_insertIdx pair.1 within, eraseIdx_insertIdx pair.1 within]
    rfl
  forwardMeasurable := Space.pair_measurable
    (MeasurableMap.comp
      (MeasurableMap.sum_elim (MeasurableMap.constant _ element fallback)
        (MeasurableMap.identity element))
      (MeasurableMap.comp (coordinate_at_measurable element)
        (Space.pair_measurable (MeasurableMap.identity _)
          (MeasurableMap.constant _ (Space.discrete Nat) index))))
    (MeasurableMap.comp (eraseIdx_measurable element)
      (Space.pair_measurable (MeasurableMap.identity _)
        (MeasurableMap.constant _ (Space.discrete Nat) index)))
  inverseMeasurable :=
    MeasurableMap.comp (insert_at_measurable element index) (Space.swap_measurable _ _)

private theorem frontLens_reference_change_within (reference : Measure element)
    (finite : Measure.SFinite reference) (fallback : α) {count index : Nat}
    (valid : index ≤ count) :
    (frontLens element fallback index).ReferenceChange
      (Measure.listPower reference finite (count + 1))
      (Measure.prod reference (Measure.listPower reference finite count)
        (Measure.SFinite.listPower finite count))
      (fun _ => Construction.Dedekind.one) := by
  classical
  have lengthAE : (Measure.listPower reference finite count).AE
      (fun values : List α => values.length = count) :=
    Measure.NullSet.mono (Measure.listPower_length_null reference finite count)
      (fun {_} failure => failure)
  unfold MeasurablePartialEquivalence.ReferenceChange
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  have movedMeasurable : ENNRealMeasurable (Space.list element)
      (ennrealIndicator (frontLens element fallback index).sourceDomain
        (fun values => function ((frontLens element fallback index).forward values))) :=
    ENNRealMeasurable.indicator (frontLens element fallback index).sourceMeasurable
      (ENNRealMeasurable.comp functionMeasurable
        (frontLens element fallback index).forwardMeasurable)
  have weightedMeasurable : ENNRealMeasurable (Space.product element (Space.list element))
      (ennrealIndicator (frontLens element fallback index).targetDomain
        (fun pair => ENNReal.mul (ENNReal.ofReal Construction.Dedekind.one) (function pair))) :=
    ENNRealMeasurable.indicator (frontLens element fallback index).targetMeasurable
      (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable)
  rw [lintegral_map _ _ _ functionMeasurable,
    ← lintegral_indicator _ _ (frontLens element fallback index).sourceMeasurable,
    ← Measure.insertIdx_power reference finite valid,
    lintegral_map _ _ _ movedMeasurable,
    lintegral_prod _ _ _ (ENNRealMeasurable.comp movedMeasurable
      (insert_at_measurable element index)),
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    ← lintegral_indicator _ _ (frontLens element fallback index).targetMeasurable,
    lintegral_prod_symm reference (Measure.listPower reference finite count) finite
      (Measure.SFinite.listPower finite count) weightedMeasurable]
  apply lintegral_congr_ae
  refine lengthAE.mono ?_
  intro rest same
  apply lintegral_congr
  intro value
  dsimp only
  have below : (frontLens element fallback index).sourceDomain
      (rest.insertIdx index value) := by
    change index < (rest.insertIdx index value).length
    rw [List.length_insertIdx_of_le_length (by omega) value]
    omega
  have within : (frontLens element fallback index).targetDomain (value, rest) := by
    change index ≤ rest.length
    omega
  rw [indicator_apply, ite_eq_left below, indicator_apply, ite_eq_left within]
  change function (Sum.elim (fun _ => fallback) (fun value => value)
      (coordinate index (rest.insertIdx index value)),
    (rest.insertIdx index value).eraseIdx index) =
    ENNReal.mul (ENNReal.ofReal Construction.Dedekind.one) (function (value, rest))
  rw [coordinate_insertIdx value (by omega), eraseIdx_insertIdx value (by omega),
    ENNReal.ofReal_one, ENNReal.one_mul]
  rfl


private theorem frontLens_reference_change_beyond (reference : Measure element)
    (finite : Measure.SFinite reference) (fallback : α) {count index : Nat}
    (beyond : count < index) :
    (frontLens element fallback index).ReferenceChange
      (Measure.listPower reference finite (count + 1))
      (Measure.prod reference (Measure.listPower reference finite count)
        (Measure.SFinite.listPower finite count))
      (fun _ => Construction.Dedekind.one) := by
  classical
  have lengthAE : ∀ length, (Measure.listPower reference finite length).AE
      (fun values : List α => values.length = length) := fun length =>
    Measure.NullSet.mono (Measure.listPower_length_null reference finite length)
      (fun {_} failure => failure)
  unfold MeasurablePartialEquivalence.ReferenceChange
  apply Measure.ext_of_lintegral
  intro function functionMeasurable
  have weightedMeasurable : ENNRealMeasurable (Space.product element (Space.list element))
      (ennrealIndicator (frontLens element fallback index).targetDomain
        (fun pair => ENNReal.mul (ENNReal.ofReal Construction.Dedekind.one) (function pair))) :=
    ENNRealMeasurable.indicator (frontLens element fallback index).targetMeasurable
      (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable)
  rw [lintegral_map _ _ _ functionMeasurable,
    ← lintegral_indicator _ _ (frontLens element fallback index).sourceMeasurable,
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    ← lintegral_indicator _ _ (frontLens element fallback index).targetMeasurable,
    lintegral_prod_symm reference (Measure.listPower reference finite count) finite
      (Measure.SFinite.listPower finite count) weightedMeasurable]
  have sourceNull : (Measure.listPower reference finite (count + 1)).AEEq
      (ennrealIndicator (frontLens element fallback index).sourceDomain
        (fun values => function ((frontLens element fallback index).forward values)))
      (fun _ => ENNReal.zero) := by
    refine (lengthAE (count + 1)).mono ?_
    intro values same
    have outside : ¬ (frontLens element fallback index).sourceDomain values := by
      change ¬ index < values.length
      omega
    rw [indicator_apply, ite_eq_right outside]
  have targetNull : (Measure.listPower reference finite count).AEEq
      (fun rest => lintegral reference (fun value =>
        ennrealIndicator (frontLens element fallback index).targetDomain
          (fun pair => ENNReal.mul (ENNReal.ofReal Construction.Dedekind.one) (function pair))
          (value, rest)))
      (fun _ => ENNReal.zero) := by
    refine (lengthAE count).mono ?_
    intro rest same
    refine (lintegral_congr _ (fun value => ?_)).trans (lintegral_zero _)
    have outside : ¬ (frontLens element fallback index).targetDomain (value, rest) := by
      change ¬ index ≤ rest.length
      omega
    rw [indicator_apply, ite_eq_right outside]
  rw [(lintegral_congr_ae sourceNull).trans (lintegral_zero _),
    (lintegral_congr_ae targetNull).trans (lintegral_zero _)]

/-- On an ordered iid power of length `count + 1`, bringing a position to the
front gives the entry's law beside the power of length `count`, with factor
one. A position past the end pairs nothing on either side. -/
theorem frontLens_reference_change (reference : Measure element)
    (finite : Measure.SFinite reference) (fallback : α) (count index : Nat) :
    (frontLens element fallback index).ReferenceChange
      (Measure.listPower reference finite (count + 1))
      (Measure.prod reference (Measure.listPower reference finite count)
        (Measure.SFinite.listPower finite count))
      (fun _ => Construction.Dedekind.one) := by
  by_cases valid : index ≤ count
  · exact frontLens_reference_change_within reference finite fallback valid
  · exact frontLens_reference_change_beyond reference finite fallback (Nat.lt_of_not_le valid)

end
end Problib.Inference
