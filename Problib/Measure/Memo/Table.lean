module

public import Problib.Measure.Memo.Decoder
public import Problib.Measure.Kernel.Product.Basic

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Real.Construction
open Problib.Measure.Real Dedekind

theorem prefix_measurable (word : List Bool) : tableSpace.Measurable (Prefix word) := by
  induction word with
  | nil => exact tableSpace.univ
  | cons value rest induction =>
      exact tableSpace.inter
        (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) 0
          (Space.discrete_measurable (Set.singleton value)))
        (Space.pi_reindex (fun _ : Nat => Space.discrete Bool) Nat.succ induction)

theorem whole_complement_null : uniform01.NullSet (Set.complement Cell.whole.region) := by
  let endpoint : UnitInterval := ⟨one, Dedekind.one_nonnegative, Dedekind.le_refl _⟩
  have nullPoint : uniform01.NullSet (Set.singleton endpoint) := uniform01_singleton endpoint
  apply nullPoint.mono
  intro seed outside
  apply Subtype.ext
  exact Dedekind.le_antisymm seed.property.2 (not_lt_iff_le.mp (fun below => outside ⟨seed.property.1, below⟩))

theorem restrict_whole : uniform01.restrict Cell.whole.region = uniform01 :=
  uniform01.restrict_eq_self_of_complement_null whole_complement_null

theorem mass_whole : uniform01 Cell.whole.region = ENNReal.one := by
  have total := congrArg (fun measure : Measure unitBorel => measure Set.univ) restrict_whole
  simpa only [Measure.restrict_apply_univ, uniform01_isProbability.univ_eq_one] using total

@[expose] noncomputable def wordWeight (bias : Bias) : List Bool → ENNReal
  | [] => ENNReal.one
  | value :: rest => ENNReal.mul (ENNReal.ofReal (Cell.weight (bias 0) value))
      (wordWeight (fun n => bias (n + 1)) rest)

theorem descend_mass (bias : Bias) (cell : Cell) (word : List Bool) :
    uniform01 (descend bias cell word).region =
      ENNReal.mul (wordWeight bias word) (uniform01 cell.region) := by
  induction word generalizing bias cell with
  | nil => exact (ENNReal.one_mul _).symm
  | cons value rest induction =>
      rw [descend, induction, Cell.mass_branch, wordWeight,
        ← ENNReal.mul_assoc, ENNReal.mul_comm (wordWeight _ rest)]

/-- A countable table law constructed from a single atomless random seed. -/
@[expose] noncomputable def law (bias : Bias) : Measure tableSpace :=
  uniform01.map (decode bias)
    (decode_measurable (fun n => MeasurableMap.constant _ _ (bias n))
      (MeasurableMap.identity _))

theorem law_probability (bias : Bias) : Measure.IsProbability (law bias) :=
  uniform01_isProbability.map (decode bias)
    (decode_measurable (fun n => MeasurableMap.constant _ _ (bias n))
      (MeasurableMap.identity _))

/-- Every finite prefix has precisely its independent Bernoulli product mass. -/
theorem law_prefix (bias : Bias) (word : List Bool) :
    law bias (Prefix word) = wordWeight bias word := by
  unfold law
  rw [Measure.map_apply uniform01 (decode bias)
    (decode_measurable (fun n => MeasurableMap.constant _ _ (bias n))
      (MeasurableMap.identity _)) (prefix_measurable word)]
  have eventMeasurable := decode_measurable
    (fun n => MeasurableMap.constant unitBorel unitBorel (bias n))
    (MeasurableMap.identity _) (prefix_measurable word)
  have equal : Set.inter (Set.preimage (decode bias) (Prefix word)) Cell.whole.region =
      (descend bias Cell.whole word).region := by
    apply Set.ext
    intro seed
    exact ⟨fun member => (prefix_read bias _ seed member.2 word).mp member.1,
      fun member => ⟨(prefix_read bias _ seed (descend_subset _ _ _ member) word).mpr member,
        descend_subset _ _ _ member⟩⟩
  have restricted := Measure.restrict_apply uniform01 Cell.whole.region eventMeasurable
  rw [restrict_whole, equal, descend_mass, mass_whole, ENNReal.mul_one] at restricted
  exact restricted

universe u
variable {α : Type u} {source : Space α}

/-- Captured parameters select the whole table law measurably. -/
@[expose] noncomputable def kernel (bias : α → Bias)
    (measurable : ∀ n, MeasurableMap source unitBorel (fun input => bias input n)) :
    Kernel source tableSpace :=
  ((Kernel.const source uniform01).attach
    (Kernel.IsSFinite.const source (Measure.SFinite.ofFinite uniform01_isProbability.to_finite))).map
      (fun pair => decode (bias pair.1) pair.2)
      (decode_measurable (fun n => MeasurableMap.comp (measurable n) (Space.first_measurable source unitBorel))
        (Space.second_measurable source unitBorel))

theorem kernel_apply (bias : α → Bias)
    (measurable : ∀ n, MeasurableMap source unitBorel (fun input => bias input n)) (input : α) :
    kernel bias measurable input = law (bias input) := by
  unfold kernel
  rw [Kernel.map_apply, Kernel.attach_apply, Kernel.const_apply, Measure.map_comp]
  rfl
  exact decode_measurable
    (fun n => MeasurableMap.comp (measurable n) (Space.first_measurable source unitBorel))
    (Space.second_measurable source unitBorel)

end
end Problib.Measure.Memo
