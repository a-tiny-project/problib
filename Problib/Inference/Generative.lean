import Problib.Probability

namespace Problib.Inference.Generative

open Problib.Probability

universe u v

structure Model (Trace : Type u) (Value : Type v) where
  traceLaw : FiniteMeasure Trace
  result : Trace → Value

/-- An arbitrary base measure supports a canonical density only through this premise. -/
def BaseMeasureFactorization {Trace : Type u}
    (base canonical : FiniteMeasure Trace) : Prop :=
  base ≈ₘ canonical

theorem density_against_factorized_base
    {Trace : Type u} [DecidableEq Trace]
    {law base canonical : FiniteMeasure Trace} {density : Trace → NNRat}
    (canonicalDensity : FiniteMeasure.IsDensity law canonical density)
    (factorization : BaseMeasureFactorization base canonical) :
    FiniteMeasure.IsDensity law base density :=
  canonicalDensity.reference_equivalent factorization

namespace Necessity

def unitDensity (_ : Bool) : NNRat :=
  1

theorem unit_density_on_canonical_base :
    FiniteMeasure.IsDensity (FiniteMeasure.dirac false)
      (FiniteMeasure.dirac false) unitDensity := by
  intro point
  cases point <;> simp [unitDensity]

theorem canonical_density_does_not_transfer_to_disjoint_base :
    ¬FiniteMeasure.IsDensity (FiniteMeasure.dirac false)
      (FiniteMeasure.dirac true) unitDensity := by
  intro hasDensity
  have impossible : (1 : NNRat) = 0 := by
    simpa [unitDensity] using hasDensity false
  exact (by decide : (1 : NNRat) ≠ 0) impossible

end Necessity

def simulate {Trace : Type u} {Value : Type v} (model : Model Trace Value)
    (density : Trace → NNRat) : FiniteMeasure (Trace × (Value × NNRat)) :=
  model.traceLaw.map fun trace => (trace, (model.result trace, density trace))

def assess {Trace : Type u} {Value : Type v} (model : Model Trace Value)
    (density : Trace → NNRat) : Trace → Value × NNRat :=
  fun trace => (model.result trace, density trace)

structure SimAssessSpecification {Trace : Type u} {Value : Type v}
    [DecidableEq Trace] [DecidableEq Value]
    (model : Model Trace Value) (reference : FiniteMeasure Trace)
    (density : Trace → NNRat)
    (simulator : FiniteMeasure (Trace × (Value × NNRat)))
    (densityEvaluator : Trace → Value × NNRat) : Prop where
  densityCorrect : FiniteMeasure.IsDensity model.traceLaw reference density
  simulatorTraceMarginal : simulator.map Prod.fst ≈ₘ model.traceLaw
  simulatorOnGraph : ∀ trace,
    simulator.mass (trace, (model.result trace, density trace)) = model.traceLaw.mass trace
  simulatorOffGraph : ∀ trace reported,
    reported ≠ (model.result trace, density trace) → simulator.mass (trace, reported) = 0
  assessorCorrect : ∀ trace,
    densityEvaluator trace = (model.result trace, density trace)

theorem simulate_trace_marginal {Trace : Type u} {Value : Type v}
    [DecidableEq Trace] [DecidableEq Value]
    (model : Model Trace Value) (density : Trace → NNRat) :
    (simulate model density).map Prod.fst ≈ₘ model.traceLaw := by
  exact FiniteMeasure.Equivalent.trans
    (FiniteMeasure.map_comp
      (fun trace => (trace, (model.result trace, density trace))) Prod.fst model.traceLaw)
    (FiniteMeasure.map_id model.traceLaw)

theorem simulate_on_graph {Trace : Type u} {Value : Type v}
    [DecidableEq Trace] [DecidableEq Value]
    (model : Model Trace Value) (density : Trace → NNRat) (trace : Trace) :
    (simulate model density).mass (trace, (model.result trace, density trace)) =
      model.traceLaw.mass trace := by
  apply FiniteMeasure.mass_map_injective
  intro left right equal
  exact congrArg Prod.fst equal

theorem simulate_off_graph {Trace : Type u} {Value : Type v}
    [DecidableEq Trace] [DecidableEq Value]
    (model : Model Trace Value) (density : Trace → NNRat)
    (trace : Trace) (reported : Value × NNRat)
    (incorrect : reported ≠ (model.result trace, density trace)) :
    (simulate model density).mass (trace, reported) = 0 := by
  apply FiniteMeasure.mass_map_no_preimage
  intro value equal
  have valueEqual : value = trace := congrArg Prod.fst equal
  subst value
  have reportedEqual : (model.result trace, density trace) = reported := congrArg Prod.snd equal
  exact incorrect reportedEqual.symm

theorem simulate_assess_finite
    {Trace : Type u} {Value : Type v} [DecidableEq Trace] [DecidableEq Value]
    (model : Model Trace Value) (reference : FiniteMeasure Trace)
    (density : Trace → NNRat)
    (densityCorrect : FiniteMeasure.IsDensity model.traceLaw reference density) :
    SimAssessSpecification model reference density (simulate model density) (assess model density) :=
  ⟨densityCorrect,
    simulate_trace_marginal model density,
    simulate_on_graph model density,
    simulate_off_graph model density,
    fun _ => rfl⟩

theorem SimAssessSpecification.of_simulator_equivalent
    {Trace : Type u} {Value : Type v} [DecidableEq Trace] [DecidableEq Value]
    {model : Model Trace Value} {reference : FiniteMeasure Trace}
    {density : Trace → NNRat}
    {simulator equivalentSimulator : FiniteMeasure (Trace × (Value × NNRat))}
    {densityEvaluator : Trace → Value × NNRat}
    (specification : SimAssessSpecification model reference density
      simulator densityEvaluator)
    (equivalent : equivalentSimulator ≈ₘ simulator) :
    SimAssessSpecification model reference density
      equivalentSimulator densityEvaluator where
  densityCorrect := specification.densityCorrect
  simulatorTraceMarginal := FiniteMeasure.Equivalent.trans
    (equivalent.map Prod.fst) specification.simulatorTraceMarginal
  simulatorOnGraph := fun trace =>
    Eq.trans (equivalent.mass_eq
      (trace, (model.result trace, density trace)))
      (specification.simulatorOnGraph trace)
  simulatorOffGraph := fun trace reported incorrect =>
    Eq.trans (equivalent.mass_eq (trace, reported))
      (specification.simulatorOffGraph trace reported incorrect)
  assessorCorrect := specification.assessorCorrect

end Problib.Inference.Generative
