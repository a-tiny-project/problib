module

public import Problib.Inference.KnowledgeCompilation.Count
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Real.Extended.Multiplication

namespace Problib.Inference.KnowledgeCompilation
public section

open Problib.Measure Problib.Real

/-- The finite independent input measure for an ordered list of Boolean labels. -/
@[expose] noncomputable def bernoulliProduct (weights : Weights ENNReal) :
    List Nat → (Nat → Bool) → Measure (Space.discrete (Nat → Bool))
  | [], assignment => Measure.dirac (Space.discrete (Nat → Bool)) assignment
  | key :: rest, assignment =>
      Measure.add
        (Measure.smul (weights key).1
          (bernoulliProduct weights rest (assign assignment key false)))
        (Measure.smul (weights key).2
          (bernoulliProduct weights rest (assign assignment key true)))

/-- The Lebesgue integral of a finite Bernoulli product is its ordered sum. -/
theorem lintegral_bernoulliProduct (weights : Weights ENNReal)
    (order : List Nat) (assignment : Nat → Bool)
    (integrand : (Nat → Bool) → ENNReal) :
    lintegral (bernoulliProduct weights order assignment) integrand =
      orderedSum ENNReal.semiring weights order assignment integrand := by
  induction order generalizing assignment with
  | nil =>
      rw [bernoulliProduct, lintegral_dirac]
      · rfl
      · intro _
        trivial
  | cons key rest induction =>
      rw [bernoulliProduct, lintegral_add_measure,
        lintegral_smul_measure, lintegral_smul_measure,
        induction (assign assignment key false),
        induction (assign assignment key true)]
      simp only [orderedSum]

/-- A checked ordered diagram has the same integral as its exact count. -/
theorem diagram_lintegral (diagram : Diagram) (order : List Nat)
    (valid : diagram.Valid order) (nodup : order.Nodup)
    (weights : Weights ENNReal) (payoff : Bool → ENNReal)
    (reference : Nat) (bound : reference < diagram.nodes.size + 2)
    (assignment : Nat → Bool) :
    lintegral (bernoulliProduct weights order assignment)
      (fun input => payoff (diagram.eval input reference)) =
      diagram.countAt ENNReal.semiring order weights payoff reference := by
  rw [lintegral_bernoulliProduct]
  exact (weighted_count_sound ENNReal.semiring diagram order valid nodup weights payoff
    reference bound assignment).symm

end
end Problib.Inference.KnowledgeCompilation
