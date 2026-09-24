module

public import Problib.Measure.Real.Generator
public import Problib.Measure.Dynkin.Uniqueness
public import Problib.Measure.Real.Continuity

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

public section

/-- Finite measures on `unitBorel` agreeing on all initial closed intervals are equal,
proved via Dynkin's π-λ theorem independently of uniform measure or quantile construction. -/
theorem finite_measure_ext_unitInitial {left right : Measure unitBorel}
    (leftFinite : Measure.IsFinite left) (rightFinite : Measure.IsFinite right)
    (agree : ∀ point, left (unitInitial point) = right (unitInitial point)) :
    left = right := by
  apply Measure.ext_of_generate unitInitials unitBorel_generated_initials
    unitInitials_pi unitInitials_univ leftFinite rightFinite
  rintro set ⟨point, rfl⟩
  exact agree point

/-- Two finite measures on `unitBorel` with equal total mass are equal when
they agree on a countable right-dense family of initial intervals.
Thresholds need not follow the fixed rational basis.
The proof uses finite-measure right-continuity and π-λ uniqueness. -/
theorem finite_measure_ext_right_dense
    {left right : Measure unitBorel}
    (leftFinite : Measure.IsFinite left) (rightFinite : Measure.IsFinite right)
    (thresholds : Nat → UnitInterval)
    (dense : ∀ point next : UnitInterval, Dedekind.lt point.val next.val →
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.le (thresholds index).val next.val)
    (total : left Set.univ = right Set.univ)
    (agree : ∀ index, left (unitInitial (thresholds index)) = right (unitInitial (thresholds index))) :
    left = right := by
  apply finite_measure_ext_unitInitial leftFinite rightFinite
  intro point
  apply ENNReal.le_antisymm
  · apply le_measure_unitInitial_of_right_dense rightFinite thresholds dense point
    · rw [← total]
      exact left.mono (Set.subset_univ _)
    · intro index above
      rw [← agree index]
      exact left.mono (fun _ member => Dedekind.le_trans member above.1)
  · apply le_measure_unitInitial_of_right_dense leftFinite thresholds dense point
    · rw [total]
      exact right.mono (Set.subset_univ _)
    · intro index above
      rw [agree index]
      exact right.mono (fun _ member => Dedekind.le_trans member above.1)


/-- Half-open intervals are closed under intersection, including empty intervals. -/
theorem halfOpenIntervals_pi : PiSystem halfOpenIntervals := by
  rintro left right ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
  refine ⟨maximum a c, minimum b d, ?_⟩
  apply Set.ext
  intro value
  change ((Dedekind.lt a value ∧ Dedekind.le value b) ∧
    (Dedekind.lt c value ∧ Dedekind.le value d)) ↔
    Dedekind.lt (maximum a c) value ∧ Dedekind.le value (minimum b d)
  rw [maximum_lt_iff, le_minimum_iff]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩,
    fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩

/-- Locally finite Borel measures are determined by their half-open intervals.
Only the right measure needs an explicit local finiteness premise. -/
theorem measure_ext_ioc {left right : Measure borel}
    (rightFinite : ∀ lower upper, ENNReal.Finite (right (Ioc lower upper)))
    (agree : ∀ lower upper, left (Ioc lower upper) = right (Ioc lower upper)) :
    left = right := by
  let generator : Set (Set Carrier) := fun set => set = Set.univ ∨ halfOpenIntervals set
  have generates : borel = Space.generated generator := by
    apply Space.ext
    intro set
    constructor
    · exact Space.generated_minimal (Space.generated generator)
        (fun {_} member => Space.generated_contains (Or.inr member))
    · apply Space.generated_minimal borel
      rintro basic (rfl | member)
      · exact borel.univ
      · exact Space.generated_contains member
  have pi : PiSystem generator := by
    rintro first second (rfl | firstMember) (rfl | secondMember)
    · exact Or.inl (Set.ext (fun _ => ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩))
    · exact Or.inr (by simpa only [Set.inter_univ_left] using secondMember)
    · exact Or.inr (by simpa only [Set.inter_univ_right] using firstMember)
    · exact Or.inr (halfOpenIntervals_pi firstMember secondMember)
  have restricted (lower upper : Carrier) :
      left.restrict (Ioc lower upper) = right.restrict (Ioc lower upper) := by
    have finiteRight : Measure.IsFinite (right.restrict (Ioc lower upper)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact rightFinite lower upper
    have finiteLeft : Measure.IsFinite (left.restrict (Ioc lower upper)) := by
      constructor
      rw [Measure.restrict_apply_univ, agree]
      exact rightFinite lower upper
    apply Measure.ext_of_generate generator generates pi (Or.inl rfl) finiteLeft finiteRight
    rintro set (rfl | member)
    · simpa only [Measure.restrict_apply_univ] using agree lower upper
    · rcases member with ⟨a, b, rfl⟩
      rw [Measure.restrict_apply _ _ (measurable_ioc a b),
        Measure.restrict_apply _ _ (measurable_ioc a b)]
      rcases halfOpenIntervals_pi (show halfOpenIntervals (Ioc a b) from ⟨a, b, rfl⟩)
        (show halfOpenIntervals (Ioc lower upper) from ⟨lower, upper, rfl⟩) with ⟨c, d, equal⟩
      rw [equal]
      exact agree c d
  let span : Nat → Set Carrier := fun n =>
    Ioc (Dedekind.neg (Dedekind.selection.ofRat (n : Rat)))
      (Dedekind.selection.ofRat (n : Rat))
  have spanMonotone : Set.MonotoneFamily span := by
    intro first second included value member
    have bound := (Dedekind.ofRat_le_iff (first : Rat) (second : Rat)).mpr
      (Rat.natCast_le_natCast.mpr included)
    exact ⟨Dedekind.lt_of_le_of_lt (Dedekind.neg_le_neg_iff.mpr bound) member.1,
      Dedekind.le_trans member.2 bound⟩
  have spanCover : Set.iUnion span = Set.univ := by
    apply Set.ext
    intro value
    constructor
    · intro _
      exact True.intro
    · intro _
      rcases Dedekind.exists_nat_strict_upper value with ⟨first, upper⟩
      rcases Dedekind.exists_nat_strict_upper (Dedekind.neg value) with ⟨second, lower⟩
      let n := max first second
      have firstLe := (Dedekind.ofRat_le_iff (first : Rat) (n : Rat)).mpr
        (Rat.natCast_le_natCast.mpr (Nat.le_max_left _ _))
      have secondLe := (Dedekind.ofRat_le_iff (second : Rat) (n : Rat)).mpr
        (Rat.natCast_le_natCast.mpr (Nat.le_max_right _ _))
      refine ⟨n, ?_, Dedekind.le_trans upper.1 firstLe⟩
      simpa only [Dedekind.neg_neg] using
        Dedekind.neg_lt_neg_iff.mpr (Dedekind.lt_of_lt_of_le lower secondLe)
  apply Measure.ext
  intro set measurable
  let slices := fun index => Set.inter set (span index)
  have slicesMeasurable : ∀ index, borel.Measurable (slices index) :=
    fun index => borel.inter measurable (measurable_ioc _ _)
  have slicesMonotone : Set.MonotoneFamily slices :=
    fun {_ _} included {_} member => ⟨member.1, spanMonotone included member.2⟩
  have slicesUnion : Set.iUnion slices = set := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨index, member⟩
      exact member.1
    · intro member
      have covered : Set.iUnion span value := by rw [spanCover]; exact True.intro
      rcases covered with ⟨index, present⟩
      exact ⟨index, member, present⟩
  have sliceEqual (index : Nat) : left (slices index) = right (slices index) := by
    have equal := congrArg (fun measure : Measure borel => measure set)
      (restricted (Dedekind.neg (Dedekind.selection.ofRat (index : Rat)))
        (Dedekind.selection.ofRat (index : Rat)))
    simpa only [Measure.restrict_apply _ _ measurable] using equal
  rw [← slicesUnion, left.continuity_from_below slices slicesMeasurable slicesMonotone,
    right.continuity_from_below slices slicesMeasurable slicesMonotone]
  exact congrArg ENNReal.iSup (funext sliceEqual)


section OpenRays

open Dedekind

/-- Finite Borel measures agreeing on open lower rays and total mass are equal. -/
theorem finite_measure_ext_iio {left right : Measure borel}
    (leftFinite : Measure.IsFinite left) (rightFinite : Measure.IsFinite right)
    (total : left Set.univ = right Set.univ)
    (rays : ∀ upper, left (Iio upper) = right (Iio upper)) : left = right := by
  let generator : Set (Set Carrier) := fun region => region = Set.univ ∨ ∃ upper, region = Iio upper
  have generates : borel = Space.generated generator := by
    have identity : MeasurableMap (Space.generated generator) borel (fun value => value) := by
      apply measurableMap_borel_iff_iio.mpr
      intro upper
      exact Space.generated_contains (Or.inr ⟨upper, rfl⟩)
    apply Space.ext
    intro region
    exact ⟨fun measurable => identity measurable,
      Space.generated_minimal borel (by
        rintro region (rfl | ⟨upper, rfl⟩)
        · exact borel.univ
        · exact measurable_iio upper)⟩
  have pi : PiSystem generator := by
    rintro first second (rfl | ⟨lower, rfl⟩) (rfl | ⟨upper, rfl⟩)
    · exact Or.inl (Set.inter_univ_left _)
    · exact Or.inr ⟨upper, Set.inter_univ_left _⟩
    · exact Or.inr ⟨lower, Set.inter_univ_right _⟩
    · rcases Dedekind.le_total lower upper with ordered | reversed
      · exact Or.inr ⟨lower, Set.ext (fun _ =>
          ⟨fun member => member.1, fun member => ⟨member, Dedekind.lt_of_lt_of_le member ordered⟩⟩)⟩
      · exact Or.inr ⟨upper, Set.ext (fun _ =>
          ⟨fun member => member.2, fun member => ⟨Dedekind.lt_of_lt_of_le member reversed, member⟩⟩)⟩
  apply Measure.ext_of_generate generator generates pi (Or.inl rfl) leftFinite rightFinite
  rintro region (rfl | ⟨upper, rfl⟩)
  · exact total
  · exact rays upper

/-- Borel measures finite on every open lower ray are determined by those ray masses.
The total mass may be infinite. -/
theorem measure_ext_iio {left right : Measure borel}
    (rightFinite : ∀ upper, ENNReal.Finite (right (Iio upper)))
    (rays : ∀ upper, left (Iio upper) = right (Iio upper)) : left = right := by
  have restricted (bound : Carrier) : left.restrict (Iio bound) = right.restrict (Iio bound) := by
    have finiteRight : Measure.IsFinite (right.restrict (Iio bound)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact rightFinite bound
    have finiteLeft : Measure.IsFinite (left.restrict (Iio bound)) := by
      constructor
      rw [Measure.restrict_apply_univ, rays bound]
      exact rightFinite bound
    apply finite_measure_ext_iio finiteLeft finiteRight
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, rays bound]
    · intro upper
      rw [Measure.restrict_apply _ _ (measurable_iio upper), Measure.restrict_apply _ _ (measurable_iio upper)]
      rcases Dedekind.le_total upper bound with ordered | reversed
      · have same : Set.inter (Iio upper) (Iio bound) = Iio upper :=
          Set.ext (fun _ => ⟨fun member => member.1, fun member => ⟨member, Dedekind.lt_of_lt_of_le member ordered⟩⟩)
        rw [same, rays upper]
      · have same : Set.inter (Iio upper) (Iio bound) = Iio bound :=
          Set.ext (fun _ => ⟨fun member => member.2, fun member => ⟨Dedekind.lt_of_lt_of_le member reversed, member⟩⟩)
        rw [same, rays bound]
  apply Measure.ext
  intro region measurable
  let slices := fun index : Nat => Set.inter region (Iio (selection.ofRat (index : Rat)))
  have slicesMeasurable : ∀ index, borel.Measurable (slices index) :=
    fun _ => borel.inter measurable (measurable_iio _)
  have slicesMonotone : Set.MonotoneFamily slices := by
    intro first second ordered value member
    exact ⟨member.1, Dedekind.lt_of_lt_of_le member.2 ((Dedekind.ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr ordered))⟩
  have cover : Set.iUnion slices = region := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨index, member⟩
      exact member.1
    · intro member
      rcases Dedekind.exists_nat_strict_upper value with ⟨index, above⟩
      exact ⟨index, member, above⟩
  have slicesEqual (index : Nat) : left (slices index) = right (slices index) := by
    have equal := congrArg (fun measure : Measure borel => measure region)
      (restricted (selection.ofRat (index : Rat)))
    simpa only [Measure.restrict_apply _ _ measurable] using equal
  rw [← cover, left.continuity_from_below slices slicesMeasurable slicesMonotone,
    right.continuity_from_below slices slicesMeasurable slicesMonotone]
  exact congrArg ENNReal.iSup (funext slicesEqual)

end OpenRays


end

end Problib.Measure.Real
