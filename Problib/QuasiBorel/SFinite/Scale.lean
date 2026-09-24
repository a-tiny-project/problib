module

public import Problib.QuasiBorel.SFinite.Score
public import Problib.QuasiBorel.SFinite.Closed

/-!
# S-finite quasi-Borel scalar multiplication

This module formalizes scalar multiplication on s-finite laws as a joint
quasi-Borel morphism `weightSpace × SFin(X) → SFin(X)`. It satisfies zero and
unit laws, scaling associativity, naturality under pushforwards, and compatibility
with monadic bind.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u v

/-- Joint quasi-Borel scalar multiplication on s-finite laws. -/
@[expose] noncomputable def scale (space : Space.{0, u} realSource) :
    Hom (Space.product weightSpace (object space)) (object space) :=
  bindContext (Hom.comp score (Space.first weightSpace (object space)))
    (Hom.comp (Space.second weightSpace (object space))
      (Space.first (Space.product weightSpace (object space)) (Space.terminal realSource)))

/-- Scalar multiplication evaluates by binding the scored weight against a constant continuation. -/
theorem scale_apply {space : Space.{0, u} realSource} (weight : ENNReal) (law : Law space) :
    scale space (weight, law) = bind (score weight)
      (Hom.constant (Space.terminal realSource) (object space) law) := by
  unfold scale
  rw [bindContext_apply]
  apply congrArg (bind (score weight))
  apply Hom.ext
  intro point
  rfl

/-- Scalar multiplication on s-finite laws agrees with measure scalar multiplication. -/
theorem scale_val {space : Space.{0, u} realSource} (weight : ENNReal) (law : Law space) :
    (scale space (weight, law)).val = Measure.smul weight law.val := by
  rw [scale_apply, bind_val, score_val, Measure.smul_bind, Measure.dirac_bind]
  rfl

@[simp] theorem scale_zero {space : Space.{0, u} realSource} (law : Law space) :
    scale space (ENNReal.zero, law) = zero space := by
  apply Law.ext
  rw [scale_val, Measure.zero_smul]
  rfl

@[simp] theorem scale_one {space : Space.{0, u} realSource} (law : Law space) :
    scale space (ENNReal.one, law) = law := by
  apply Law.ext
  rw [scale_val, Measure.one_smul]

@[simp] theorem scale_zero_law (space : Space.{0, u} realSource) (weight : ENNReal) :
    scale space (weight, zero space) = zero space := by
  rw [scale_apply]
  exact bind_zero (score weight)

theorem scale_scale {space : Space.{0, u} realSource} (first second : ENNReal) (law : Law space) :
    scale space (first, scale space (second, law)) = scale space (ENNReal.mul first second, law) := by
  apply Law.ext
  rw [scale_val, scale_val, scale_val, Measure.smul_smul]

theorem scale_natural {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (function : Hom domain codomain) (weight : ENNReal) (law : Law domain) :
    map function (scale domain (weight, law)) = scale codomain (weight, map function law) := by
  apply Law.ext
  rw [map_val, scale_val, scale_val, map_val, Measure.map_smul]

theorem scale_bind {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (weight : ENNReal) (law : Law domain) (kernel : Hom domain (object codomain)) :
    scale codomain (weight, bind law kernel) = bind (scale domain (weight, law)) kernel := by
  apply Law.ext
  rw [scale_val, bind_val, bind_val, scale_val, Measure.smul_bind]

theorem mass_scale {space : Space.{0, u} realSource} (weight : ENNReal) (law : Law space) :
    mass space (scale space (weight, law)) = ENNReal.mul weight (mass space law) := by
  rw [mass_apply, scale_val,
    Measure.smul_apply_measurable _ _ (by exact space.toMeasurable.univ)]
  rfl

theorem score_bind {space : Space.{0, u} realSource} (weight : ENNReal)
    (kernel : Hom (Space.terminal realSource) (object space)) :
    bind (score weight) kernel = scale space (weight, kernel ()) := by
  apply Law.ext
  rw [bind_val, score_val, Measure.smul_bind, Measure.dirac_bind, scale_val]
  rfl

theorem scale_pure {space : Space.{0, u} realSource} (weight : ENNReal) (point : space.Carrier) :
    scale space (weight, pure space point) =
      map (Hom.constant (Space.terminal realSource) space point) (score weight) := by
  apply Law.ext
  rw [scale_val, pure_val, map_val, score_val, Measure.map_smul, Measure.map_dirac]
  rfl

theorem score_sequence (first second : ENNReal) :
    bind (score first) (Hom.constant (Space.terminal realSource)
      (object (Space.terminal realSource)) (score second)) = score (ENNReal.mul first second) := by
  rw [score_bind]
  change scale (Space.terminal realSource) (first, score second) = score (ENNReal.mul first second)
  apply Law.ext
  rw [scale_val, score_val, score_val, Measure.smul_smul]

theorem bind_const {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (law : Law domain) (other : Law codomain) :
    bind law (Hom.constant domain (object codomain) other) = scale codomain (mass domain law, other) := by
  apply Law.ext
  rw [bind_val, scale_val]
  have equal : toKernel (Hom.constant domain (object codomain) other) =
      Kernel.const domain.toMeasurable other.val := by
    apply Kernel.ext
    intro point
    rfl
  rw [equal, Measure.bind_const]
  rfl

end

end Problib.QuasiBorel.SFinite
