module
public import Problib.Measure.Space.Countable
public import Problib.Measure.Product

set_option autoImplicit false
namespace Problib.Measure
public section
universe u v w
variable {ι : Type u} {β : ι → Type v} {γ : Type w}

namespace Space
/-- A region of a dependent sum is measurable precisely when each slice is. -/
@[expose] def sigma (spaces : ∀ index, Space (β index)) : Space (Sigma β) where
  Measurable := fun region => ∀ index, (spaces index).Measurable (fun value => region ⟨index, value⟩)
  empty := fun index => (spaces index).empty
  complement := fun measurable index => (spaces index).complement (measurable index)
  iUnion := fun measurable index => (spaces index).iUnion (fun n => measurable n index)
end Space

/-- The payload of a dependent pair at one index, or a default at any other. -/
@[expose] def sigmaSlice [DecidableEq ι] (index : ι) (default : β index) (point : Sigma β) :
    β index :=
  if same : point.1 = index then same ▸ point.2 else default

public theorem sigmaSlice_eq [DecidableEq ι] {index : ι} (default : β index) {point : Sigma β}
    (same : point.1 = index) : point = ⟨index, sigmaSlice index default point⟩ := by
  obtain ⟨first, value⟩ := point
  subst same
  simp [sigmaSlice]

namespace MeasurableMap
public theorem sigma_mk (spaces : ∀ index, Space (β index)) (index : ι) :
    MeasurableMap (spaces index) (Space.sigma spaces) (Sigma.mk index) := by
  intro region measurable
  exact measurable index

public theorem from_sigma_iff {spaces : ∀ index, Space (β index)} {target : Space γ}
    {function : Sigma β → γ} :
    MeasurableMap (Space.sigma spaces) target function ↔
      ∀ index, MeasurableMap (spaces index) target (fun value => function ⟨index, value⟩) := by
  constructor
  · intro measurable index
    exact MeasurableMap.comp measurable (sigma_mk spaces index)
  · intro measurable region regionMeasurable index
    exact measurable index regionMeasurable

/-- A countable tag lets the preimage of each dependent slice be assembled. -/
public theorem into_sigma {α : Type w} {source : Space α}
    {spaces : ∀ index, Space (β index)} (code : ι → Nat)
    (injective : Function.Injective code) {tag : α → ι}
    (tagMeasurable : MeasurableMap source (Space.discrete ι) tag)
    {payload : ∀ index, α → β index}
    (payloadMeasurable : ∀ index, MeasurableMap source (spaces index) (payload index)) :
    MeasurableMap source (Space.sigma spaces)
      (fun input => ⟨tag input, payload (tag input) input⟩) := by
  intro region regionMeasurable
  have pieces : ∀ index, source.Measurable
      (fun input => tag input = index ∧ region ⟨index, payload index input⟩) := by
    intro index
    exact source.inter
      (tagMeasurable (Space.discrete_measurable (fun selected => selected = index)))
      (payloadMeasurable index (regionMeasurable index))
  have union := Space.i_union_of_nat_injection source code injective _ pieces
  have same : (fun input => region ⟨tag input, payload (tag input) input⟩) =
      (fun input => ∃ index, tag input = index ∧ region ⟨index, payload index input⟩) := by
    apply Set.ext
    intro input
    constructor
    · intro member; exact ⟨tag input, rfl, member⟩
    · rintro ⟨index, equal, member⟩
      cases equal
      exact member
  change source.Measurable (fun input => region ⟨tag input, payload (tag input) input⟩)
  rw [same]
  exact union

public theorem sigma_slice [DecidableEq ι] (spaces : ∀ index, Space (β index)) (index : ι)
    (default : β index) : MeasurableMap (Space.sigma spaces) (spaces index) (sigmaSlice index default) := by
  intro region measurable other
  change (spaces other).Measurable fun value => region (sigmaSlice index default ⟨other, value⟩)
  by_cases same : other = index
  · subst same
    simpa [sigmaSlice] using measurable
  · simp only [sigmaSlice, same, dite_false]
    exact MeasurableMap.constant (spaces other) (spaces index) default measurable

public theorem sigma_fst (spaces : ∀ index, Space (β index)) :
    MeasurableMap (Space.sigma spaces) (Space.discrete ι) Sigma.fst :=
  fun {region} _ other => MeasurableMap.constant (spaces other) (Space.discrete ι) other
    (set := region) trivial

/-- A map into a dependent sum is measurable when its tag is, and when on each
tag's fiber its payload agrees with a measurable map. A fiber whose payload type
is empty is empty, so only inhabited payload types need a map. -/
public theorem into_sigma_of_slices [DecidableEq ι] {α : Type w} {source : Space α}
    {spaces : ∀ index, Space (β index)} (code : ι → Nat) (injective : Function.Injective code)
    {function : α → Sigma β}
    (tagMeasurable : MeasurableMap source (Space.discrete ι) (fun input => (function input).1))
    (slices : ∀ index (default : β index), ∃ slice : α → β index,
      MeasurableMap source (spaces index) slice ∧
        ∀ input, (function input).1 = index → slice input = sigmaSlice index default (function input)) :
    MeasurableMap source (Space.sigma spaces) function := by
  intro region regionMeasurable
  have pieces : ∀ index, source.Measurable
      (fun input => (function input).1 = index ∧ region (function input)) := by
    intro index
    by_cases inhabited : Nonempty (β index)
    · obtain ⟨slice, sliceMeasurable, agree⟩ := slices index (Classical.choice inhabited)
      have equal : (fun input => (function input).1 = index ∧ region (function input)) =
          (fun input => (function input).1 = index ∧ region ⟨index, slice input⟩) := by
        funext input
        apply propext
        constructor <;> rintro ⟨same, member⟩ <;> refine ⟨same, ?_⟩
        · rwa [agree input same, ← sigmaSlice_eq _ same]
        · rwa [agree input same, ← sigmaSlice_eq _ same] at member
      rw [equal]
      exact source.inter (tagMeasurable (Space.discrete_measurable (fun tag => tag = index)))
        (sliceMeasurable (regionMeasurable index))
    · have equal : (fun input => (function input).1 = index ∧ region (function input)) = Set.empty := by
        funext input
        apply propext
        refine ⟨fun ⟨same, _⟩ => inhabited ⟨same ▸ (function input).2⟩, False.elim⟩
      rw [equal]
      exact source.empty
  have equal : Set.preimage function region =
      (fun input => ∃ index, (function input).1 = index ∧ region (function input)) := by
    funext input
    exact propext ⟨fun member => ⟨_, rfl, member⟩, fun ⟨_, _, member⟩ => member⟩
  rw [equal]
  exact Space.i_union_of_nat_injection source code injective _ pieces

/-- Pairing a parameter with a dependent pair distributes into every fiber. -/
public theorem sigma_distribute [DecidableEq ι] {α : Type w} {spaces : ∀ index, Space (β index)}
    {parameter : Space α} (code : ι → Nat) (injective : Function.Injective code) :
    MeasurableMap (Space.product (Space.sigma spaces) parameter)
      (Space.sigma fun index => Space.product (spaces index) parameter)
      (fun input => (⟨input.1.1, input.1.2, input.2⟩ : Σ index, β index × α)) := by
  apply into_sigma_of_slices code injective
  · exact MeasurableMap.comp (sigma_fst spaces) (Space.first_measurable _ _)
  · intro index default
    refine ⟨fun input => (sigmaSlice index default.1 input.1, input.2), ?_, ?_⟩
    · exact Space.pair_measurable
        (MeasurableMap.comp (sigma_slice spaces index default.1) (Space.first_measurable _ _))
        (Space.second_measurable _ _)
    · rintro ⟨⟨first, value⟩, captured⟩ same
      subst same
      simp [sigmaSlice]
end MeasurableMap
end
end Problib.Measure
