module

public import Problib.QuasiBorel.SFinite.Random

set_option autoImplicit false

/-!
# Dirac unit for s-finite quasi-Borel spaces

This module defines the Dirac unit for s-finite quasi-Borel spaces.
It proves that Dirac lifts are represented laws and assemble into a canonical
quasi-Borel morphism, independently of general kernel composition.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v w

/-- Constructs the Dirac point-mass law at any point of a quasi-Borel space. -/
@[expose] noncomputable def pure (space : Space realSource) (point : space.Carrier) : Law space := by
  let seed := Problib.Real.Construction.Dedekind.zero
  refine ⟨Measure.dirac space.toMeasurable point, ?_⟩
  refine ⟨Presentation.total (fun _ => point) (space.constant point)
    (Measure.dirac borel seed) (Measure.SFinite.ofFinite (Measure.IsFinite.dirac borel seed)), ?_⟩
  rw [Presentation.total_toMeasure]
  exact Measure.map_dirac (fun _ => point) (Space.random_measurable (space.constant point)) seed

/-- Proves that the pure law evaluates to the Dirac measure. -/
@[simp] theorem pure_val (space : Space realSource) (point : space.Carrier) :
    (pure space point).val = Measure.dirac space.toMeasurable point := rfl

/-- Canonical quasi-Borel unit morphism embedding points as Dirac laws. -/
@[expose] noncomputable def unit (space : Space realSource) : Hom space (object space) where
  toFun := pure space
  map_random := by
    intro random accepted
    refine ⟨{
      random := fun seed => Sum.inr (random seed)
      accepted := SumRandom.inr accepted
      kernel := Kernel.deterministic (fun seed => seed) (MeasurableMap.identity borel)
      sfinite := Kernel.IsSFinite.deterministic (fun seed => seed) (MeasurableMap.identity borel)
      law := ?_
    }⟩
    intro seed
    change (Presentation.total random accepted (Measure.dirac borel seed)
      (Measure.SFinite.ofFinite (Measure.IsFinite.dirac borel seed))).toMeasure = _
    rw [Presentation.total_toMeasure]
    exact Measure.map_dirac random (Space.random_measurable accepted) seed

/-- Proves that the transition kernel induced by the unit is the identity kernel. -/
@[simp] theorem toKernel_unit (space : Space realSource) :
    toKernel (unit space) = Kernel.deterministic (fun point => point)
      (MeasurableMap.identity space.toMeasurable) := by
  apply Kernel.ext
  intro point
  rfl

end

end Problib.QuasiBorel.SFinite
