module

public import Problib.QuasiBorel.SFinite.Generator
public import Problib.QuasiBorel.Measurable.Embedding
public import Problib.Measure.StandardBorel.Real

set_option autoImplicit false

/-!
# Standard-Borel generators and decoders for s-finite quasi-Borel spaces

This module constructs standard-Borel random seed spaces from partial
generators and establishes equivalence with standard-Borel generators.
Decoders avoid requiring target inhabitants by selecting fallbacks within
accepted random inputs to the success domain.
-/

namespace Problib.QuasiBorel.SFinite.Generator

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

variable {space : Space realSource}

/-- The measurable subset of real seeds mapped into the target carrier. -/
@[expose] def successes (generator : Generator space) : Set Carrier :=
  Set.preimage generator.random
    (Set.range (Space.inrEmbedding (Space.terminal realSource) space).function)

/-- Proves that the success domain is a Borel-measurable subset of the reals. -/
theorem successes_measurable (generator : Generator space) :
    borel.Measurable generator.successes :=
  Space.random_measurable generator.accepted
    (Space.inrEmbedding (Space.terminal realSource) space).range_measurable

/-- The subtype of real seeds falling within the generator success domain. -/
abbrev Seed (generator : Generator space) := {seed : Carrier // generator.successes seed}

/-- The measurable subspace induced on the success domain from the real Borel line. -/
@[expose] def seedSpace (generator : Generator space) : Problib.Measure.Space generator.Seed :=
  Problib.Measure.Space.comap (fun seed : generator.Seed => seed.val) borel

/-- The measurable subtype embedding from the success domain into the real Borel line. -/
@[expose] def seedEmbedding (generator : Generator space) :
    MeasurableEmbedding generator.seedSpace borel :=
  MeasurableEmbedding.subtype generator.successes generator.successes_measurable

/-- Proves that the success seed space is standard Borel through real Borel embedding. -/
@[expose] noncomputable def seed_standardBorel (generator : Generator space) :
    StandardBorel generator.seedSpace :=
  StandardBorel.ofEmbedding generator.seedEmbedding StandardBorel.real

/-- Extracts a target point from an accepted success seed. -/
@[expose] noncomputable def decode (generator : Generator space) (seed : generator.Seed) :
    space.Carrier :=
  Classical.choose seed.property

/-- Proves that decoding an accepted seed recovers the generator evaluation. -/
theorem decode_spec (generator : Generator space) (seed : generator.Seed) :
    (Sum.inr (generator.decode seed) : (withFailure space).Carrier) = generator.random seed.val :=
  Classical.choose_spec seed.property

/-- The quasi-Borel morphism decoding the standard-Borel seed space into the target space. -/
@[expose] noncomputable def decoder (generator : Generator space) :
    Hom (Space.ofMeasurable borel generator.seedSpace) space where
  toFun := generator.decode
  map_random := by
    intro random measurable
    let fallback := generator.decode (random Problib.Real.Construction.Dedekind.zero)
    let recover : Hom (withFailure space) space :=
      Space.copair (Hom.constant (Space.terminal realSource) space fallback) (Hom.identity space)
    have inclusion : MeasurableMap borel borel (fun seed => (random seed).val) :=
      MeasurableMap.comp generator.seedEmbedding.measurable measurable
    have accepted := recover.map_random ((withFailure space).reparam inclusion generator.accepted)
    have equal : (fun seed => recover (generator.random (random seed).val)) =
        (fun seed => generator.decode (random seed)) := by
      funext seed
      rw [← generator.decode_spec (random seed)]
      rfl
    rw [equal] at accepted
    exact accepted

/-- Proves that the decoder is measurable into the induced measurable space. -/
theorem decode_measurable (generator : Generator space) :
    MeasurableMap generator.seedSpace space.toMeasurable generator.decode := by
  have measurable : MeasurableMap
      (Space.ofMeasurable borel generator.seedSpace).toMeasurable
      space.toMeasurable generator.decode := generator.decoder.toMeasurable
  rw [Space.toMeasurable_of_embedding generator.seedEmbedding] at measurable
  exact @measurable

/-- Relates the embedded preimage under decode to the generator random preimage. -/
theorem image_decode_preimage (generator : Generator space) (region : Set space.Carrier) :
    Set.image generator.seedEmbedding.function (Set.preimage generator.decode region) =
      Set.preimage generator.random
        (Set.image (Space.inrEmbedding (Space.terminal realSource) space).function region) := by
  apply Set.ext
  intro input
  constructor
  · rintro ⟨seed, member, equal⟩
    refine ⟨generator.decode seed, member, ?_⟩
    change Sum.inr (generator.decode seed) = generator.random input
    rw [← equal]
    exact generator.decode_spec seed
  · rintro ⟨point, member, equal⟩
    let seed : generator.Seed := ⟨input, point, equal⟩
    refine ⟨seed, ?_, rfl⟩
    have same : generator.decode seed = point :=
      Sum.inr.inj ((generator.decode_spec seed).trans equal.symm)
    change region (generator.decode seed)
    rw [same]
    exact member

end

end Problib.QuasiBorel.SFinite.Generator

namespace Problib.QuasiBorel.SFinite.Standard

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v

/-- Total random generator from an arbitrary standard-Borel source into a quasi-Borel space. -/
structure Generator (space : Space.{0, u} realSource) where
  Seed : Type v
  source : Problib.Measure.Space Seed
  standard : StandardBorel source
  random : Hom (Space.ofMeasurable borel source) space

namespace Generator

variable {space : Space.{0, u} realSource}

/-- Proves that any standard-Borel generator is measurable into the induced measurable space. -/
theorem measurable (generator : Generator.{u, v} space) :
    MeasurableMap generator.source space.toMeasurable generator.random :=
  generator.random.toMeasurable_of_embedding generator.standard.embeddingReal

/-- Embeds a standard-Borel generator into a partial generator from the real line. -/
@[expose] noncomputable def toPartial (generator : Generator.{u, v} space) :
    SFinite.Generator space := by
  classical
  exact if inhabited : Nonempty generator.Seed then
    let fallback := Classical.choice inhabited
    { random := fun seed => Sum.inr
        (generator.random (generator.standard.embeddingReal.retract fallback seed))
      accepted := SumRandom.inr (generator.random.map_random
        (generator.standard.embeddingReal.retract_measurable fallback)) }
  else
    { random := fun _ => Sum.inl ()
      accepted := (withFailure space).constant (Sum.inl ()) }

/-- Proves that partial transport on embedded seeds recovers the standard generator. -/
theorem toPartial_forward (generator : Generator.{u, v} space) (point : generator.Seed) :
    generator.toPartial.random (generator.standard.embeddingReal.function point) =
      Sum.inr (generator.random point) := by
  classical
  simp only [toPartial, dif_pos (show Nonempty generator.Seed from ⟨point⟩),
    MeasurableEmbedding.retract_forward]

/-- Constructs a standard-Borel generator from a partial real generator. -/
@[expose] noncomputable def ofPartial (generator : SFinite.Generator space) :
    Generator.{u, 0} space where
  Seed := generator.Seed
  source := generator.seedSpace
  standard := generator.seed_standardBorel
  random := generator.decoder

end Generator

end

end Problib.QuasiBorel.SFinite.Standard
