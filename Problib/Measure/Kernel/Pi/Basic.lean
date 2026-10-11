module

public import Problib.Measure.Kernel.Pi.Law
public import Problib.Measure.Kernel.Randomization.StandardBorel
public import Problib.Measure.Memo.Sequence

set_option autoImplicit false

/-!
# Countable products of probability kernels

A probability kernel with a uniform randomizer runs once per key of a countable
key type. Each key reads its own seed from one sequence of independent uniform
seeds and pushes that seed through the randomizer at that key. Every key then
has the body's law at that key, and distinct keys are independent. Every
probability kernel into a standard Borel space has such a randomizer. Product
laws are unique, so the product kernel depends neither on the randomizer nor on
the key coding.
-/

namespace Problib.Measure.Kernel
public section
open Problib.Real Problib.Measure.Real

universe u v w x
variable {α : Type u} {κ : Type v} {β : Type w}
  {source : Space α} {keySpace : Space κ} {target : Space β}

/-- Every key's draw is measurable in the input and the seed sequence. -/
theorem draws_measurable {body : Kernel (Space.product keySpace source) target}
    (selection : Randomizer body) (encode : κ → Nat) :
    MeasurableMap (Space.product source (Space.pi fun _ : Nat => unitBorel))
      (Space.pi fun _ : κ => target)
      (fun pair key => selection.function ((key, pair.1), pair.2 (encode key))) :=
  Space.pi_measurable fun key => MeasurableMap.comp selection.measurable
    (Space.pair_measurable
      (Space.pair_measurable (MeasurableMap.constant _ keySpace key)
        (Space.first_measurable source (Space.pi fun _ : Nat => unitBorel)))
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Nat => unitBorel) (encode key))
        (Space.second_measurable source (Space.pi fun _ : Nat => unitBorel))))

/-- At one input, one key's draw is measurable in the seed sequence. -/
theorem draw_measurable {body : Kernel (Space.product keySpace source) target}
    (selection : Randomizer body) (encode : κ → Nat) (input : α) (key : κ) :
    MeasurableMap (Space.pi fun _ : Nat => unitBorel) target
      (fun seeds => selection.function ((key, input), seeds (encode key))) :=
  MeasurableMap.comp (selection.fiber_measurable (key, input))
    (Space.coordinate_measurable (fun _ : Nat => unitBorel) (encode key))

/-- The countable product of a randomized kernel: at each input, every key
draws from the body at that key with its own seed from one sequence of
independent uniform seeds. -/
@[expose] noncomputable def pi {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (selection : Randomizer body) :
    Kernel source (Space.pi fun _ : κ => target) :=
  ((Kernel.const source Memo.uniformSequence).attach
    (Kernel.IsSFinite.const source
      (Measure.SFinite.ofFinite Memo.uniformSequence_probability.to_finite))).map
    (fun pair key => selection.function ((key, pair.1), pair.2 (encode key)))
    (draws_measurable selection encode)

/-- At one input, the product kernel pushes the seed sequence through every
key's draw. -/
theorem pi_apply {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (selection : Randomizer body) (input : α) :
    Kernel.pi encode selection input =
      Memo.uniformSequence.map
        (fun seeds key => selection.function ((key, input), seeds (encode key)))
        (Space.pi_measurable fun key => draw_measurable selection encode input key) :=
  Measure.map_comp Memo.uniformSequence (fun seeds => (input, seeds))
    (fun pair key => selection.function ((key, pair.1), pair.2 (encode key)))
    (Kernel.pair_left_measurable (source := source)
      (target := Space.pi fun _ : Nat => unitBorel) input)
    (draws_measurable selection encode)

/-- The product kernel is a probability kernel. -/
theorem pi_probability {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (selection : Randomizer body) (input : α) :
    (Kernel.pi encode selection input).IsProbability := by
  rw [pi_apply]
  exact Memo.uniformSequence_probability.map _
    (Space.pi_measurable fun key => draw_measurable selection encode input key)

/-- The product kernel is finite, with bound one. -/
theorem pi_finite {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (selection : Randomizer body) :
    Kernel.IsFinite (Kernel.pi encode selection) := by
  refine ⟨⟨ENNReal.one, trivial, ?_⟩⟩
  intro input
  rw [(pi_probability encode selection input).univ_eq_one]
  exact ENNReal.le_refl _

/-- Each coordinate of the product kernel has the body's law at its key. -/
theorem pi_coordinate {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (selection : Randomizer body) (input : α) (key : κ) :
    (Kernel.pi encode selection input).map (fun point => point key)
        (Space.coordinate_measurable (fun _ : κ => target) key) = body (key, input) := by
  have seedLaw := Memo.uniformSequence_isProduct.coordinate (encode key)
  rw [pi_apply]
  refine (Measure.map_comp Memo.uniformSequence
      (fun seeds key => selection.function ((key, input), seeds (encode key)))
      (fun point => point key)
      (Space.pi_measurable fun key => draw_measurable selection encode input key)
      (Space.coordinate_measurable (fun _ : κ => target) key)).trans ?_
  refine Eq.trans ?_ (selection.law (key, input))
  refine (Measure.map_comp Memo.uniformSequence (fun seeds => seeds (encode key))
    (fun seed => selection.function ((key, input), seed))
    (Space.coordinate_measurable (fun _ : Nat => unitBorel) (encode key))
    (selection.fiber_measurable (key, input))).symm.trans ?_
  rw [seedLaw]

/-- At each input, the product kernel's law is the product of the body's laws
at the keys: each key draws from the body at that key, and distinct keys are
independent. -/
theorem pi_isProduct {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (injective : Function.Injective encode) (selection : Randomizer body)
    (input : α) :
    Pi.IsProduct (Kernel.pi encode selection input) fun key => body (key, input) := by
  have product := ((Memo.uniformSequence_isProduct.reindex encode injective).map
    (fun key seed => selection.function ((key, input), seed))
    fun key => selection.fiber_measurable (key, input)).congr_laws
      fun key => selection.law (key, input)
  have equal := (pi_apply encode selection input).trans
    (Measure.map_comp Memo.uniformSequence (fun seeds key => seeds (encode key))
      (fun seeds key => selection.function ((key, input), seeds key))
      (Space.pi_reindex (fun _ : Nat => unitBorel) encode)
      (Space.pi_map (functions := fun key seed => selection.function ((key, input), seed))
        fun key => selection.fiber_measurable (key, input))).symm
  rw [equal]
  exact product

/-- Distinct keys of the product kernel draw independently: a joint event on
two of them has the product of their masses. -/
theorem pi_pair {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (injective : Function.Injective encode) (selection : Randomizer body)
    (input : α) {first second : κ} (different : first ≠ second) {firstSet secondSet : Set β}
    (firstMeasurable : target.Measurable firstSet)
    (secondMeasurable : target.Measurable secondSet) :
    Kernel.pi encode selection input
        (fun point => firstSet (point first) ∧ secondSet (point second)) =
      ENNReal.mul (body (first, input) firstSet) (body (second, input) secondSet) :=
  (pi_isProduct encode injective selection input).pair different firstMeasurable
    secondMeasurable

/-- The joint law of two distinct keys of the product kernel is the product of
the body's laws at those keys. -/
theorem pi_independent {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (injective : Function.Injective encode) (selection : Randomizer body)
    (input : α) {first second : κ} (different : first ≠ second) :
    (Kernel.pi encode selection input).map (fun point => (point first, point second))
        (Space.pair_measurable (Space.coordinate_measurable (fun _ : κ => target) first)
          (Space.coordinate_measurable (fun _ : κ => target) second)) =
      Measure.prod (body (first, input)) (body (second, input))
        (Measure.SigmaFinite.ofFinite (selection.isProbability (second, input)).to_finite).toSFinite :=
  (pi_isProduct encode injective selection input).pair_prod different

/-- A kernel whose law at every input is the product of the body's laws is the
product kernel. -/
theorem pi_unique {body : Kernel (Space.product keySpace source) target}
    (encode : κ → Nat) (injective : Function.Injective encode) (selection : Randomizer body)
    {kernel : Kernel source (Space.pi fun _ : κ => target)}
    (product : ∀ input, Pi.IsProduct (kernel input) fun key => body (key, input)) :
    kernel = Kernel.pi encode selection :=
  Kernel.ext fun input => (product input).ext (pi_isProduct encode injective selection input)

/-- Two product kernels agree at two inputs when their bodies agree at every key
there, whatever their input spaces and randomizers. -/
theorem pi_apply_congr {γ : Type x} {other : Space γ}
    {left : Kernel (Space.product keySpace source) target}
    {right : Kernel (Space.product keySpace other) target}
    (encode : κ → Nat) (injective : Function.Injective encode)
    (leftSelection : Randomizer left) (rightSelection : Randomizer right)
    (input : α) (otherInput : γ) (equal : ∀ key, left (key, input) = right (key, otherInput)) :
    Kernel.pi encode leftSelection input = Kernel.pi encode rightSelection otherInput :=
  (pi_isProduct encode injective leftSelection input).ext
    ((pi_isProduct encode injective rightSelection otherInput).congr_laws
      fun key => (equal key).symm)

/-- The product kernel depends only on its body: neither the key coding nor the
randomizer changes it. -/
theorem pi_congr {left right : Kernel (Space.product keySpace source) target}
    (equal : left = right) {leftEncode rightEncode : κ → Nat}
    (leftInjective : Function.Injective leftEncode)
    (rightInjective : Function.Injective rightEncode)
    (leftSelection : Randomizer left) (rightSelection : Randomizer right) :
    Kernel.pi leftEncode leftSelection = Kernel.pi rightEncode rightSelection := by
  subst equal
  exact pi_unique rightEncode rightInjective rightSelection
    (pi_isProduct leftEncode leftInjective leftSelection)

/-- Every probability kernel into a standard Borel space has a countable
product over any key type that injects into the naturals. -/
theorem exists_pi_of_standardBorel (encode : κ → Nat) (injective : Function.Injective encode)
    (body : Kernel (Space.product keySpace source) target) (presentation : StandardBorel target)
    (normalized : ∀ input, (body input).IsProbability) :
    ∃ kernel : Kernel source (Space.pi fun _ : κ => target),
      ∀ input, Pi.IsProduct (kernel input) fun key => body (key, input) :=
  ⟨Kernel.pi encode (Randomizer.ofStandardBorel body presentation normalized),
    pi_isProduct encode injective _⟩

end
end Problib.Measure.Kernel
