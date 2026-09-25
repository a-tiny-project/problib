module

public import Problib.Measure.Disintegration.Pushforward
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Kernel.RadonNikodym.Basic
public import Problib.Measure.Kernel.Finite
public import Problib.Measure.Kernel.Measurable

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v w
variable {α : Type u} {τ : Type v} {β : Type w}
  {source : Space α} {trace : Space τ} {result : Space β}
  {ret : α × τ → β}
  {reference : Kernel source trace}
  {retMeasurable : MeasurableMap (Space.product source trace) result ret}

/-- The contextual graph joint, with trace first and return second. -/
@[expose] public noncomputable def graphJoint (reference : Kernel source trace)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret)
    (input : α) : Measure (Space.product trace result) :=
  Measure.graphJoint (reference input) (fun point => ret (input, point))
    (section_measurable retMeasurable input)

/-- The extra regularity a pointwise choice of disintegrations does not supply. -/
@[expose] public def ConditionalMeasurable
    (selection : ∀ input, Measure.Disintegration
      (graphJoint reference retMeasurable input)) : Prop :=
  ∀ ⦃set⦄, trace.Measurable set →
    ENNRealMeasurable (Space.product source result)
      (fun pair => (selection pair.1).conditional pair.2 set)

/-- Fibers disintegrate the graph at each source input and vary measurably
with source input and return. No separate concentration certificate is used. -/
public structure FiberReference (reference : Kernel source trace)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret) where
  selection : ∀ input, Measure.Disintegration
    (graphJoint reference retMeasurable input)
  measurable : ConditionalMeasurable selection
  finite : ∀ input output, Measure.IsFinite
    ((selection input).conditional output)

/-- The selected conditionals form one kernel because of the named premise. -/
@[expose] public noncomputable def FiberReference.conditional
    (fiber : FiberReference reference retMeasurable) :
    Kernel (Space.product source result) trace where
  toFun := fun pair => (fiber.selection pair.1).conditional pair.2
  measurable := by
    intro set setMeasurable
    exact fiber.measurable setMeasurable

@[expose] public noncomputable def FiberReference.conditionalSFinite
    (fiber : FiberReference reference retMeasurable) :
    IsSFinite fiber.conditional :=
  IsSFinite.ofFiniteFibers (fun pair => by
    change Measure.IsFinite ((fiber.selection pair.1).conditional pair.2)
    exact fiber.finite pair.1 pair.2)

/-- Probability fibers are required by the sampler rule, not by exact
pushforward density. -/
@[expose] public def FiberReference.IsMarkov
    (fiber : FiberReference reference retMeasurable) : Prop :=
  ∀ pair, Measure.IsProbability (fiber.conditional pair)

/-- The trace reference pushed along the return, pointwise in input. -/
@[expose] public noncomputable def imageReference
    (reference : Kernel source trace) (finite : IsSFinite reference)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret) :
    Kernel source result :=
  (reference.attach finite).map ret retMeasurable

public theorem imageReference_apply (reference : Kernel source trace)
    (finite : IsSFinite reference)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret)
    (input : α) :
    imageReference reference finite retMeasurable input =
      (reference input).map (fun point => ret (input, point))
        (section_measurable retMeasurable input) := by
  rw [imageReference, Kernel.map_apply, Kernel.attach_apply,
    Measure.map_comp]

@[expose] public noncomputable def fiberDensity
    (fiber : FiberReference reference retMeasurable)
    (density : α → τ → ENNReal) : α → β → ENNReal :=
  fun input output => lintegral (fiber.conditional (input, output))
    (density input)

/-- The key joint measurability proof. The integrand is p(input, trace),
not a function of output except through the conditional kernel. -/
public theorem fiberDensity_measurable
    (fiber : FiberReference reference retMeasurable)
    {density : α → τ → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source trace)
      (fun pair => density pair.1 pair.2)) :
    ENNRealMeasurable (Space.product source result)
      (fun pair => fiberDensity fiber density pair.1 pair.2) := by
  let lift : (α × β) × τ → α × τ :=
    fun pair => (pair.1.1, pair.2)
  have liftMeasurable :
      MeasurableMap (Space.product (Space.product source result) trace)
        (Space.product source trace) lift := by
    apply Space.pair_measurable
    · exact MeasurableMap.comp (Space.first_measurable source result)
        (Space.first_measurable (Space.product source result) trace)
    · exact Space.second_measurable (Space.product source result) trace
  have liftedDensity : ENNRealMeasurable
      (Space.product (Space.product source result) trace)
      (fun pair => density pair.1.1 pair.2) := by
    simpa only [lift] using densityMeasurable.comp liftMeasurable
  have integralMeasurable :=
    Kernel.lintegral_measurable_joint fiber.conditional
      fiber.conditionalSFinite
      (function := fun pair point => density pair.1 point) liftedDensity
  simpa only [fiberDensity] using integralMeasurable

/-- Exact density transport along the contextual graph disintegration. -/
public theorem density_map_of_fiber
    {kernel : Kernel source result} {joint : Kernel source trace}
    (presents : Presents kernel joint ret retMeasurable)
    (referenceFinite : IsSFinite reference)
    (fiber : FiberReference reference retMeasurable)
    (derivative : RadonNikodymDerivative joint reference) :
    ENNRealMeasurable (Space.product source result)
      (fun pair => fiberDensity fiber derivative.density pair.1 pair.2) ∧
      ∀ input, Measure.IsDensity (kernel input)
        (imageReference reference referenceFinite retMeasurable input)
        (fiberDensity fiber derivative.density input) := by
  constructor
  · exact fiberDensity_measurable fiber derivative.density_measurable
  · intro input
    have pointwise := Measure.density_pushforward_of_disintegration
      (reference input) (fun point => ret (input, point))
      (section_measurable retMeasurable input) (fiber.selection input)
      (jointly_measurable_slice derivative.density_measurable input)
    change Measure.IsDensity (kernel input)
      (imageReference reference referenceFinite retMeasurable input)
      (fiberDensity fiber derivative.density input)
    rw [imageReference_apply]
    rw [← presents input, derivative.reconstruct input]
    change Measure.IsDensity
      (((reference input).withDensity (derivative.density input)).map
        (fun point => ret (input, point))
        (section_measurable retMeasurable input))
      ((reference input).map (fun point => ret (input, point))
        (section_measurable retMeasurable input))
      (fun y => lintegral ((fiber.selection input).conditional y)
        (derivative.density input))
    exact pointwise

@[expose] public noncomputable def FiberReference.derivative
    {kernel : Kernel source result} {joint : Kernel source trace}
    (presents : Presents kernel joint ret retMeasurable)
    (referenceFinite : IsSFinite reference)
    (fiber : FiberReference reference retMeasurable)
    (derivative : RadonNikodymDerivative joint reference) :
    RadonNikodymDerivative kernel
      (imageReference reference referenceFinite retMeasurable) where
  density := fiberDensity fiber derivative.density
  density_measurable := (density_map_of_fiber presents referenceFinite fiber derivative).1
  reconstruct := (density_map_of_fiber presents referenceFinite fiber derivative).2

/-- Identity return has Dirac fibers. -/
@[expose] public noncomputable def FiberReference.identity
    (reference : Kernel source result) :
    FiberReference (ret := fun pair => pair.2) reference
      (Space.second_measurable source result) where
  selection := by
    intro input
    refine ⟨Kernel.deterministic (fun value => value)
      (MeasurableMap.identity result), ?_, ?_⟩
    · exact IsSFinite.ofFiniteFibers
        (fun output => Measure.IsFinite.dirac result output)
    · change Measure.reverseSemiproduct
        (Measure.secondMarginal
          (Measure.graphJoint (reference input) (fun value => value)
            (MeasurableMap.identity result)))
        (Kernel.deterministic (fun value => value)
          (MeasurableMap.identity result)) _ =
        Measure.graphJoint (reference input) (fun value => value)
          (MeasurableMap.identity result)
      rw [Measure.secondMarginal_graphJoint]
      rw [Measure.map_id (reference input)]
      apply Measure.ext
      intro E hE
      have diagonalMeasurable : MeasurableMap result
          (Space.product result result) (fun value => (value, value)) :=
        Space.pair_measurable (MeasurableMap.identity result)
          (MeasurableMap.identity result)
      have regionMeasurable : result.Measurable
          (Set.preimage (fun value => (value, value)) E) :=
        diagonalMeasurable hE
      calc
        Measure.reverseSemiproduct (reference input)
            (Kernel.deterministic (fun value => value)
              (MeasurableMap.identity result)) _ E =
          lintegral (reference input) (fun output =>
            Kernel.deterministic (fun value => value)
              (MeasurableMap.identity result) output
              (Set.preimage (fun first => (first, output)) E)) :=
          Measure.reverseSemiproduct_apply _ _ _ hE
        _ = lintegral (reference input)
            (ennrealIndicator (Set.preimage (fun value => (value, value)) E)
              (fun _ => ENNReal.one)) := by
          apply lintegral_congr
          intro output
          rw [Kernel.deterministic_apply]
          have sectionMeasurable : result.Measurable
              (Set.preimage (fun first => (first, output)) E) :=
            (Space.pair_measurable (MeasurableMap.identity result)
              (MeasurableMap.constant result result output)) hE
          rw [Measure.dirac_apply result output sectionMeasurable]
          rfl
        _ = (reference input)
            (Set.preimage (fun value => (value, value)) E) :=
          (Measure.apply_eq_lintegral_indicator _ regionMeasurable).symm
        _ = Measure.graphJoint (reference input) id
            (MeasurableMap.identity result) E :=
          (Measure.map_apply _ _ diagonalMeasurable hE).symm
  measurable := by
    intro E hE
    have base : ENNRealMeasurable result
        (fun output => Measure.dirac result output E) :=
      (Kernel.deterministic (fun value => value)
        (MeasurableMap.identity result)).measurable hE
    change ENNRealMeasurable (Space.product source result)
      (fun pair => Measure.dirac result pair.2 E)
    exact base.comp (Space.second_measurable source result)
  finite := by
    intro input output
    exact Measure.IsFinite.dirac result output

public theorem FiberReference.identity_isMarkov
    (reference : Kernel source result) :
    (FiberReference.identity reference).IsMarkov := by
  intro pair
  change Measure.IsProbability (Measure.dirac result pair.2)
  exact Measure.IsProbability.dirac result pair.2

/-- Standard Borel fibers are repaired to probabilities; the caller supplies
joint measurability of the selected family. -/
@[expose] public noncomputable def FiberReference.ofStandardBorel
    (reference : Kernel source trace)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret)
    (presentation : StandardBorel trace)
    (finite : ∀ input, Measure.SigmaFinite
      (Measure.secondMarginal (graphJoint reference retMeasurable input)))
    (fallback : τ)
    (measurable : ConditionalMeasurable
      (fun input => Measure.Disintegration.ofStandardBorelProbability
        (graphJoint reference retMeasurable input) presentation
        (finite input) fallback)) :
    FiberReference reference retMeasurable where
  selection := fun input => Measure.Disintegration.ofStandardBorelProbability
    (graphJoint reference retMeasurable input) presentation
    (finite input) fallback
  measurable := measurable
  finite := by
    intro input output
    exact (Measure.Disintegration.ofStandardBorelProbability_isProbability
      (graphJoint reference retMeasurable input) presentation
      (finite input) fallback output).to_finite

public theorem FiberReference.ofStandardBorel_isMarkov
    (reference : Kernel source trace)
    (retMeasurable : MeasurableMap (Space.product source trace) result ret)
    (presentation : StandardBorel trace)
    (finite : ∀ input, Measure.SigmaFinite
      (Measure.secondMarginal (graphJoint reference retMeasurable input)))
    (fallback : τ)
    (measurable : ConditionalMeasurable
      (fun input => Measure.Disintegration.ofStandardBorelProbability
        (graphJoint reference retMeasurable input) presentation
        (finite input) fallback)) :
    (FiberReference.ofStandardBorel reference retMeasurable presentation
      finite fallback measurable).IsMarkov := by
  intro pair
  change Measure.IsProbability ((Measure.Disintegration.ofStandardBorelProbability
    (graphJoint reference retMeasurable pair.1) presentation
    (finite pair.1) fallback).conditional pair.2)
  exact Measure.Disintegration.ofStandardBorelProbability_isProbability
    (graphJoint reference retMeasurable pair.1) presentation
    (finite pair.1) fallback pair.2

end Problib.Measure.Kernel
