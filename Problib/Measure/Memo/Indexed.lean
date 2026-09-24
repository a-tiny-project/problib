module

public import Problib.Measure.Memo.Kernel

set_option autoImplicit false

namespace Problib.Measure.Memo.Indexed
public section
open Problib.Real Problib.Measure.Real

universe u v
variable {κ : Type u} {α : Type v} {source : Space α}

@[expose] def space (κ : Type u) : Space (κ → Bool) :=
  Space.pi (fun _ : κ => Space.discrete Bool)

/-- Unused natural codes have a deterministic false fact. -/
@[expose] noncomputable def extendBias (decode : Nat → Option κ) (bias : κ → UnitInterval) : Bias :=
  fun n => match decode n with
    | none => unitZero
    | some key => bias key

theorem extendBias_encode (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval) (key : κ) :
    extendBias decode bias (encode key) = bias key := by
  simp only [extendBias, roundTrip]

theorem encode_injective (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) : Function.Injective encode := by
  intro left right equal
  have decoded := congrArg decode equal
  simpa only [roundTrip, Option.some.injEq] using decoded

@[expose] noncomputable def law (encode : κ → Nat) (decode : Nat → Option κ)
    (bias : κ → UnitInterval) : Measure (space κ) :=
  (Memo.law (extendBias decode bias)).map (fun table key => table (encode key))
    (Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode)

theorem law_probability (encode : κ → Nat) (decode : Nat → Option κ) (bias : κ → UnitInterval) :
    Measure.IsProbability (law encode decode bias) :=
  (Memo.law_probability _).map _ (Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode)

theorem law_coordinate_true (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key) (bias : κ → UnitInterval) (key : κ) :
    law encode decode bias (fun table => table key = true) = ENNReal.ofReal (bias key).val := by
  have mapped := Measure.map_apply (Memo.law (extendBias decode bias))
    (fun table : Table => fun key : κ => table (encode key))
    (show MeasurableMap tableSpace (space κ) _ from
      Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode)
    (show (space κ).Measurable (fun table => table key = true) from
      Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key
        (Space.discrete_measurable (Set.singleton true)))
  exact mapped.trans ((Memo.law_coordinate_true (extendBias decode bias) (encode key)).trans
    (congrArg (fun p : UnitInterval => ENNReal.ofReal p.val)
      (extendBias_encode encode decode roundTrip bias key)))

theorem extendBias_measurable (decode : Nat → Option κ) (bias : α → κ → UnitInterval)
    (measurable : ∀ key, MeasurableMap source unitBorel (fun input => bias input key)) (n : Nat) :
    MeasurableMap source unitBorel (fun input => extendBias decode (bias input) n) := by
  intro event eventMeasurable
  cases decoded : decode n with
  | none => simpa only [extendBias, decoded] using
      MeasurableMap.constant source unitBorel unitZero eventMeasurable
  | some key => simpa only [extendBias, decoded] using measurable key eventMeasurable

@[expose] noncomputable def kernel (encode : κ → Nat) (decode : Nat → Option κ)
    (bias : α → κ → UnitInterval)
    (measurable : ∀ key, MeasurableMap source unitBorel (fun input => bias input key)) :
    Kernel source (space κ) :=
  (Memo.kernel (fun input => extendBias decode (bias input)) (extendBias_measurable decode bias measurable)).map
    (fun table key => table (encode key)) (Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode)

theorem kernel_apply (encode : κ → Nat) (decode : Nat → Option κ) (bias : α → κ → UnitInterval)
    (measurable : ∀ key, MeasurableMap source unitBorel (fun input => bias input key)) (input : α) :
    kernel encode decode bias measurable input = law encode decode (bias input) := by
  exact congrArg (fun measure : Measure tableSpace => measure.map
    (fun table key => table (encode key))
    (show MeasurableMap tableSpace (space κ) _ from
      Space.pi_reindex (fun _ : Nat => Space.discrete Bool) encode))
    (Memo.kernel_apply _ (extendBias_measurable decode bias measurable) input)

variable {keySpace : Space κ}

@[expose] noncomputable def ofBody (encode : κ → Nat) (decode : Nat → Option κ)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) : Kernel source (space κ) :=
  kernel encode decode (bodyBias body) (bodyBias_measurable body)

theorem ofBody_apply (encode : κ → Nat) (decode : Nat → Option κ)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) (input : α) :
    ofBody encode decode body input = law encode decode (bodyBias body input) := kernel_apply _ _ _ _ _

theorem ofBody_probability (encode : κ → Nat) (decode : Nat → Option κ)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) (input : α) :
    Measure.IsProbability (ofBody encode decode body input) := by
  rw [ofBody_apply]
  exact law_probability _ _ _

theorem ofBody_finite (encode : κ → Nat) (decode : Nat → Option κ)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool)) :
    Kernel.IsFinite (ofBody encode decode body) := by
  refine ⟨⟨ENNReal.one, trivial, ?_⟩⟩
  intro input
  rw [(ofBody_probability encode decode body input).univ_eq_one]
  exact ENNReal.le_refl _

theorem ofBody_coordinate (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool))
    (probability : ∀ input, Measure.IsProbability (body input)) (input : α) (key : κ) :
    (ofBody encode decode body input).map (fun table => table key)
      (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key) = body (key, input) := by
  apply Measure.IsProbability.bool_ext
    ((ofBody_probability encode decode body input).map _ (Space.coordinate_measurable _ key)) (probability _)
  rw [Measure.map_apply (ofBody encode decode body input) (fun table : κ → Bool => table key)
    (Space.coordinate_measurable (fun _ : κ => Space.discrete Bool) key)
    (Space.discrete_measurable (Set.singleton true)), ofBody_apply]
  change law encode decode _ (fun table => table key = true) = _
  rw [law_coordinate_true encode decode roundTrip]
  exact ofReal_unitClamp_of_le ((probability _).apply_le_one _)

theorem ofBody_apply_congr {β : Type v} {target : Space β}
    (encode : κ → Nat) (decode : Nat → Option κ)
    (left : Kernel (Space.product keySpace source) (Space.discrete Bool))
    (right : Kernel (Space.product keySpace target) (Space.discrete Bool))
    (input : α) (other : β) (equal : ∀ key, left (key, input) = right (key, other)) :
    ofBody encode decode left input = ofBody encode decode right other := by
  rw [ofBody_apply, ofBody_apply]
  apply congrArg (law encode decode)
  funext key
  exact congrArg (fun measure => unitClamp (measure (Set.singleton true))) (equal key)

end
end Problib.Measure.Memo.Indexed
