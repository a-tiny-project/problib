module

public import Problib.Measure.Uniform
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Real.Construction
open Problib.Measure.Real
open Dedekind

/-- A half-open cell inside the unit interval. Empty cells retain their endpoints. -/
structure Cell where
  lower : Carrier
  upper : Carrier
  nonnegative : le zero lower
  ordered : le lower upper
  bounded : le upper one

namespace Cell

@[expose] noncomputable def whole : Cell := ⟨zero, one, Dedekind.le_refl _, Dedekind.one_nonnegative, Dedekind.le_refl _⟩

@[expose] noncomputable def width (cell : Cell) : Carrier := sub cell.upper cell.lower

@[expose] noncomputable def cut (cell : Cell) (bias : UnitInterval) : Carrier :=
  add cell.lower (mul bias.val cell.width)

private theorem add_sub (left right : Carrier) : add left (sub right left) = right := by
  rw [Dedekind.sub_eq_add_neg, Dedekind.add_left_comm, Dedekind.add_neg, Dedekind.add_zero]

theorem width_nonnegative (cell : Cell) : le zero cell.width :=
  Dedekind.sub_nonnegative cell.ordered

theorem lower_cut (cell : Cell) (bias : UnitInterval) : le cell.lower (cell.cut bias) := by
  have bound := @Dedekind.add_le_add_left_iff zero (mul bias.val cell.width) cell.lower |>.mpr
    (Dedekind.mul_nonnegative bias.property.1 cell.width_nonnegative)
  simpa only [cut, Dedekind.add_zero] using bound

theorem cut_upper (cell : Cell) (bias : UnitInterval) : le (cell.cut bias) cell.upper := by
  have bound := Dedekind.mul_le_mul_nonnegative_right bias.property.2 cell.width_nonnegative
  rw [Dedekind.mul_comm one, Dedekind.mul_one] at bound
  have added := @Dedekind.add_le_add_left_iff _ _ cell.lower |>.mpr bound
  simpa only [cut, width, add_sub] using added

/-- True takes the left subinterval, whose relative length is the bias. -/
@[expose] noncomputable def branch (cell : Cell) (bias : UnitInterval) : Bool → Cell
  | true => ⟨cell.lower, cell.cut bias, cell.nonnegative, cell.lower_cut bias,
      Dedekind.le_trans (cell.cut_upper bias) cell.bounded⟩
  | false => ⟨cell.cut bias, cell.upper,
      Dedekind.le_trans cell.nonnegative (cell.lower_cut bias), cell.cut_upper bias, cell.bounded⟩

@[expose] def region (cell : Cell) : Set UnitInterval :=
  fun seed => le cell.lower seed.val ∧ lt seed.val cell.upper

theorem region_measurable (cell : Cell) : unitBorel.Measurable cell.region :=
  unitInclusion_measurable (measurable_ico cell.lower cell.upper)

theorem mass (cell : Cell) : uniform01 cell.region = ENNReal.ofReal cell.width := by
  have restricted : Set.inter (Ico cell.lower cell.upper) unitSet =
      Ico cell.lower cell.upper := by
    apply Set.ext
    intro point
    exact ⟨fun member => member.1, fun member => ⟨member,
      Dedekind.le_trans cell.nonnegative member.1, Dedekind.le_trans member.2.1 cell.bounded⟩⟩
  have mapped := Measure.map_apply uniform01 unitInclusion unitInclusion_measurable
    (measurable_ico cell.lower cell.upper)
  rw [uniform01_map_unitInclusion, restrictedUnit, Measure.restrict_apply _ _ (measurable_ico cell.lower cell.upper),
    restricted, volume_ico] at mapped
  exact mapped.symm

theorem branch_region (cell : Cell) (bias : UnitInterval) (seed : UnitInterval)
    (inside : cell.region seed) (value : Bool) :
    (cell.branch bias value).region seed ↔
      boolIndicator (fun point : UnitInterval => lt point.val (cell.cut bias)) seed = value := by
  classical
  cases value with
  | false =>
      change (le (cell.cut bias) seed.val ∧ lt seed.val cell.upper) ↔ _
      rw [boolIndicator, decide_eq_false_iff_not, not_lt_iff_le]
      exact ⟨And.left, fun bound => ⟨bound, inside.2⟩⟩
  | true =>
      change (le cell.lower seed.val ∧ lt seed.val (cell.cut bias)) ↔ _
      rw [boolIndicator, decide_eq_true_eq]
      exact ⟨And.right, fun bound => ⟨inside.1, bound⟩⟩

theorem branch_subset (cell : Cell) (bias : UnitInterval) (value : Bool) :
    ∀ seed, (cell.branch bias value).region seed → cell.region seed := by
  intro seed inside
  cases value with
  | false => exact ⟨Dedekind.le_trans (cell.lower_cut bias) inside.1, inside.2⟩
  | true => exact ⟨inside.1, Dedekind.lt_of_lt_of_le inside.2 (cell.cut_upper bias)⟩

/-- The relative mass of the selected Boolean branch. -/
@[expose] noncomputable def weight (bias : UnitInterval) : Bool → Carrier
  | true => bias.val
  | false => sub one bias.val

theorem weight_nonnegative (bias : UnitInterval) (value : Bool) :
    le zero (weight bias value) := by
  cases value
  · exact Dedekind.sub_nonnegative bias.property.2
  · exact bias.property.1

theorem width_branch (cell : Cell) (bias : UnitInterval) (value : Bool) :
    (cell.branch bias value).width = mul (weight bias value) cell.width := by
  cases value with
  | true =>
      change sub (add cell.lower (mul bias.val cell.width)) cell.lower = _
      rw [Dedekind.sub_eq_add_neg, Dedekind.add_comm cell.lower, Dedekind.add_assoc, Dedekind.add_neg, Dedekind.add_zero]
      rfl
  | false =>
      change sub cell.upper (add cell.lower (mul bias.val cell.width)) =
        mul (sub one bias.val) cell.width
      have neg_add (x y : Carrier) : neg (add x y) = add (neg x) (neg y) :=
        Problib.Algebra.AdditiveCommutativeGroupLaws.neg_add_distrib additive.group x y
      have add_mul (x y z : Carrier) : mul (add x y) z = add (mul x z) (mul y z) :=
        multiplicativeSelection.ring.add_mul x y z
      have neg_mul (x y : Carrier) : mul (neg x) y = neg (mul x y) :=
        multiplicativeSelection.ring.neg_mul x y
      rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg, neg_add, ← Dedekind.add_assoc,
        add_mul, neg_mul, Dedekind.mul_comm one, Dedekind.mul_one]
      rfl

theorem mass_branch (cell : Cell) (bias : UnitInterval) (value : Bool) :
    uniform01 (cell.branch bias value).region =
      ENNReal.mul (ENNReal.ofReal (weight bias value)) (uniform01 cell.region) := by
  rw [mass, mass, width_branch,
    ofReal_mul (weight_nonnegative bias value) cell.width_nonnegative]

end Cell
end
end Problib.Measure.Memo
