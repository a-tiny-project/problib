module

public import Foundations.QuasiBorel.SFinite.Score
public import Foundations.QuasiBorel.SFinite.Monad

/-!
# Mass interactions with monadic operations and terminal discard

This module proves total mass preservation under pushforward maps, integration
under monadic bind, normalization preservation for pure and mapped laws, and
the terminal discard identity identifying discarding to the terminal space with
the score of total mass.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Real (ENNReal)

universe u v

/-- Pushforward along a quasi-Borel morphism preserves total mass. -/
theorem mass_map {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (function : Hom domain codomain) (law : Law domain) :
    mass codomain (map function law) = mass domain law :=
  map_univ function law

/-- Total mass of a monadic bind equals the lower integral of the continuation's mass. -/
theorem mass_bind {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (law : Law domain) (kernel : Hom domain (object codomain)) :
    mass codomain (bind law kernel) = lintegral law.val (fun point => mass codomain (kernel point)) := by
  rw [mass_apply, bind_val, Measure.bind_apply _ _ (by exact codomain.toMeasurable.univ)]
  rfl

theorem pure_probability (space : Space.{0, u} realSource) (point : space.Carrier) :
    Measure.IsProbability (pure space point).val :=
  Measure.IsProbability.dirac space.toMeasurable point

theorem map_probability {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (function : Hom domain codomain) (law : Law domain) :
    Measure.IsProbability (map function law).val ↔ Measure.IsProbability law.val := by
  constructor
  · intro normalized
    exact ⟨(map_univ function law).symm.trans normalized.univ_eq_one⟩
  · intro normalized
    exact ⟨(map_univ function law).trans normalized.univ_eq_one⟩

theorem bind_probability {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (law : Law domain) (kernel : Hom domain (object codomain))
    (normalized : Measure.IsProbability law.val)
    (fibers : ∀ point, Measure.IsProbability (kernel point).val) :
    Measure.IsProbability (bind law kernel).val :=
  normalized.bind (toKernel kernel) fibers

/-- Discarding to the terminal space equals the score of the law's total mass. -/
theorem discard {space : Space.{0, u} realSource} (law : Law space) :
    map (Space.terminate space) law = score (mass space law) := by
  rw [← mass_map (Space.terminate space) law, score_mass]

/-- Discarding to the terminal space yields the Dirac unit iff the law has mass one. -/
theorem discard_probability_iff {space : Space.{0, u} realSource} (law : Law space) :
    map (Space.terminate space) law = pure (Space.terminal realSource) () ↔
      Measure.IsProbability law.val := by
  rw [discard, ← score_one]
  constructor
  · intro equal
    exact ⟨score_injective equal⟩
  · intro normalized
    exact congrArg score normalized.univ_eq_one

end

end Foundations.QuasiBorel.SFinite
