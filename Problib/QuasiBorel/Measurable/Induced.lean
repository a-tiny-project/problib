module

public import Problib.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Induced measurable space on a quasi-Borel space carrier whose measurable
sets have measurable preimages under all accepted random elements. -/
@[expose] def Space.toMeasurable {source : Problib.Measure.Space Ω}
    (space : Space (Source.ofMeasurable source)) : Problib.Measure.Space space.Carrier where
  Measurable := fun region => ∀ {random}, space.Random random →
    source.Measurable (Set.preimage random region)
  empty := by
    intro random accepted
    exact source.empty
  complement := by
    intro region measurable random accepted
    exact source.complement (measurable accepted)
  iUnion := by
    intro regions measurable random accepted
    exact source.iUnion (fun index => measurable index accepted)

theorem Space.random_measurable {source : Problib.Measure.Space Ω}
    {space : Space (Source.ofMeasurable source)} {random : Ω → space.Carrier}
    (accepted : space.Random random) :
    MeasurableMap source space.toMeasurable random := by
  intro region measurable
  exact measurable accepted

/-- Quasi-Borel morphisms induce measurable maps between the induced
measurable spaces. -/
theorem Hom.toMeasurable {source : Problib.Measure.Space Ω}
    {domain codomain : Space (Source.ofMeasurable source)} (morphism : Hom domain codomain) :
    MeasurableMap (Space.toMeasurable domain) (Space.toMeasurable codomain) morphism := by
  intro region measurable random accepted
  exact measurable (morphism.map_random accepted)

/-- A map from an induced space to an arbitrary measurable space is measurable
if and only if its precomposition with every accepted random element is measurable. -/
theorem Space.measurableMap_iff_random {source : Problib.Measure.Space Ω}
    {domain : Space (Source.ofMeasurable source)} {codomain : Problib.Measure.Space β}
    {function : domain.Carrier → β} :
    MeasurableMap (Space.toMeasurable domain) codomain function ↔
      ∀ {random}, domain.Random random →
        MeasurableMap source codomain (fun seed => function (random seed)) := by
  constructor
  · intro measurable random accepted region regionMeasurable
    exact measurable regionMeasurable accepted
  · intro randomMeasurable region regionMeasurable random accepted
    exact randomMeasurable accepted regionMeasurable

end

end Problib.QuasiBorel
