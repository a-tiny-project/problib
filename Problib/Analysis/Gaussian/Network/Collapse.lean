module

public import Problib.Analysis.Gaussian.Network.Condition
public import Problib.Measure.Integral.Density.Change
import Problib.Real.Grind

/-! Collapsing a Gaussian observation of a linear-Gaussian network.

An observation `y ~ N(c + ⟨a, x⟩, q)` of the nodes `x` weights the network's
law by its likelihood. The weighted law is the evidence at `y` times the law
of an updated network (`score_collapse`). The update appends the observation
as a last node, moves it to the front by adjacent reversals, and instantiates
it at `y` (`Network.update`). The evidence is the front node's Gaussian
density at `y`, kept at the instantiation. It is positive and finite
(`evidence_positive_finite`).

The proof is pointwise in densities and follows the update's own steps: the
appended network's density at `x ++ [y]` is the network's density times the
likelihood, the reversals carry it to `y :: x`, and `density_cons` splits off
the evidence.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Moving the last node to the front -/

/-- The word `[n - 1, …, 0]` that moves node `n` to the front. -/
@[expose] public def frontWord : Nat → List Nat
  | 0 => []
  | count + 1 => count :: frontWord count

public theorem swapAt_middle {α : Type} (front : List α) (first second : α) (rest : List α) :
    swapAt front.length (front ++ first :: second :: rest) = front ++ second :: first :: rest := by
  induction front with
  | nil => rfl
  | cons head front induction =>
      simp only [List.length_cons, List.cons_append, swapAt, induction]

/-- The front word moves the entry after the first `n` to the front. -/
public theorem permute_frontWord {α : Type} {count : Nat} {front : List α} (value : α)
    (rest : List α) (counted : front.length = count) :
    permute (frontWord count) (front ++ value :: rest) = value :: (front ++ rest) := by
  induction count generalizing front rest with
  | zero =>
      rw [List.length_eq_zero_iff] at counted
      subst counted
      rfl
  | succ count induction =>
      have nonempty : front ≠ [] := fun empty => by simp [empty] at counted
      obtain ⟨initial, last, rfl⟩ : ∃ initial last, front = initial ++ [last] :=
        ⟨front.dropLast, front.getLast nonempty, (List.dropLast_concat_getLast nonempty).symm⟩
      have initialCounted : initial.length = count := by
        simp only [List.length_append, List.length_singleton] at counted
        omega
      have swapped := swapAt_middle initial last value rest
      rw [initialCounted] at swapped
      change permute (frontWord count) (swapAt count (initial ++ [last] ++ value :: rest)) = _
      rw [List.append_assoc, List.singleton_append, swapped,
        induction (last :: rest) initialCounted]
      simp

/-! ### Observations and the update -/

/-- A Gaussian observation `y ~ N(c + ⟨a, x⟩, q)` of the network's nodes. -/
public structure Observation (network : Network) where
  intercept : Carrier
  coefficients : List Carrier
  shaped : coefficients.length = network.length
  variance : Carrier
  positive : lt zero variance

namespace Observation

variable {network : Network}

/-- The observation as a row regressing on every node. -/
@[expose] public def row (observation : Observation network) : Row where
  intercept := observation.intercept
  coefficients := observation.coefficients
  variance := observation.variance

/-- The likelihood of `y` at the nodes `x`. -/
@[expose] public def likelihood (observation : Observation network) (values : List Carrier)
    (observed : Carrier) : ENNReal :=
  ENNReal.finite (Gaussian.density (add observation.intercept (dot observation.coefficients values))
    observation.variance observed)

public theorem likelihood_measurable (observation : Observation network) (observed : Carrier) :
    ENNRealMeasurable (Space.list borel) (fun values => observation.likelihood values
      observed) := by
  have pairing : MeasurableMap (Space.list borel) (Space.product (Space.list borel) borel)
      (fun values => (values, observed)) :=
    Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ borel observed)
  have composed := ENNRealMeasurable.comp observation.row.pairDensity_measurable pairing
  exact composed

/-- The network with the observation appended as its last node. -/
@[expose] public def joint (observation : Observation network) : Network :=
  network.append observation.row observation.shaped observation.positive

/-- The joint network with the observation moved to the front. -/
@[expose] public def front (observation : Observation network) : Network :=
  observation.joint.reverseAlong (frontWord network.length)

public theorem front_length (observation : Observation network) :
    observation.front.length = network.length + 1 := by
  unfold front
  rw [Network.length_reverseAlong]
  exact Network.length_append _ _ _ _

public theorem front_nonempty (observation : Observation network) :
    0 < observation.front.length := by
  rw [front_length]
  exact Nat.succ_pos _

/-- The evidence at `y`: the front node's Gaussian density at `y`. -/
@[expose] public def evidence (observation : Observation network) (observed : Carrier) : ENNReal :=
  observation.front.rootDensity observation.front_nonempty observed

public theorem evidence_positive_finite (observation : Observation network) (observed : Carrier) :
    ENNReal.lt ENNReal.zero (observation.evidence observed) ∧
      observation.evidence observed ≠ ENNReal.top :=
  observation.front.rootDensity_positive observation.front_nonempty observed

end Observation

/-- The network updated by an observation at `y`: append the observation, move
it to the front, and instantiate it at `y`. -/
@[expose] public def Network.update (network : Network) (observation : Observation network)
    (observed : Carrier) : Network :=
  observation.front.instantiateFirst observed

@[simp] public theorem Network.length_update (network : Network) (observation : Observation network)
    (observed : Carrier) : (network.update observation observed).length = network.length := by
  unfold Network.update
  rw [Network.length_instantiateFirst, observation.front_length, Nat.add_sub_cancel]

/-- Pointwise collapse: the density times the likelihood is the evidence times
the updated density. -/
public theorem Observation.collapse_density {network : Network} (observation : Observation network)
    (observed : Carrier) (values : List Carrier) :
    ENNReal.mul (ENNReal.finite (network.density values)) (observation.likelihood values observed) =
      ENNReal.mul (observation.evidence observed)
        (ENNReal.finite ((network.update observation observed).density values)) := by
  by_cases counted : values.length = network.length
  · have joint := network.density_append observation.row observation.shaped observation.positive
      (values, observed)
    have moved := observation.joint.density_reverseAlong (frontWord network.length)
      (snoc (values, observed))
    have front : permute (frontWord network.length) (snoc (values, observed)) =
        observed :: values := by
      have permuted := permute_frontWord observed [] counted
      rw [List.append_nil] at permuted
      exact permuted
    have split := observation.front.density_cons observation.front_nonempty observed values
    change _ = ENNReal.mul (observation.front.rootDensity observation.front_nonempty observed)
      (observation.front.restDensity (observed, values))
    rw [← split]
    unfold Observation.front
    rw [← front, moved]
    unfold Observation.joint
    rw [joint, ENNReal.mul_comm]
    rfl
  · have vanished : network.density values = NNReal.zero := by
      unfold Network.density
      rw [ite_eq_right counted]
    have updatedVanished : (network.update observation observed).density values = NNReal.zero := by
      unfold Network.density
      rw [Network.length_update, ite_eq_right counted]
    rw [vanished, updatedVanished]
    unfold Observation.likelihood Observation.evidence Network.rootDensity
    rw [ENNReal.finite_mul_finite, ENNReal.finite_mul_finite, NNReal.zero_mul, NNReal.mul_zero]

/-- Score collapse: weighting the network's law by the observation's likelihood
at `y` is the evidence at `y` times the updated network's law. -/
public theorem Network.score_collapse (network : Network) (observation : Observation network)
    (observed : Carrier) :
    network.law.withDensity (fun values => observation.likelihood values observed) =
      Measure.smul (observation.evidence observed) (network.update observation observed).law := by
  rw [network.law_eq_withDensity, (network.update observation observed).law_eq_withDensity,
    Network.length_update,
    Measure.smul_withDensity _ _ (network.update observation observed).density_measurable,
    Measure.withDensity_withDensity _ network.density_measurable
      (observation.likelihood_measurable observed)]
  congr 1
  funext values
  exact observation.collapse_density observed values

end
end Problib.Analysis.Gaussian
