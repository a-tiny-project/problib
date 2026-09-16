module

public import Foundations.QuasiBorel.SFinite.Scale
public import Foundations.Measure.Integral.Density.Change
public import Foundations.Measure.Extended.Algebra.Binary

/-!
# S-finite density reweighting and weighted-point kernels

This module formalizes deterministic density reweighting as a joint higher-order
quasi-Borel morphism for densities given by morphisms into `weightSpace`.
It proves exact agreement with measure density modification
(`Measure.withDensity`), naturality, repeated reweighting, and bind interactions
for arbitrary weights, including zero and infinity, without finite bounds.
It also proves a global s-finite kernel certificate for the deterministic
weighted-point kernel on its induced parameter space.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Real (ENNReal)

universe u v

/-- Quasi-Borel multiplication morphism on extended nonnegative weights. -/
@[expose] noncomputable def weightMul : Hom (Space.product weightSpace weightSpace) weightSpace where
  toFun := fun point => ENNReal.mul point.1 point.2
  mapRandom := by
    intro random accepted
    exact ((ENNRealMeasurable.ofMeasurableMap accepted.1).mul
      (ENNRealMeasurable.ofMeasurableMap accepted.2)).measurableMap

/-- Scaled Dirac point-mass morphism mapping a weight and point to an s-finite law. -/
@[expose] noncomputable def weightedPoint (space : Space.{0, u} realSource) :
    Hom (Space.product weightSpace space) (object space) :=
  Hom.comp (scale space) (Space.productMap (Hom.identity weightSpace) (unit space))

theorem weightedPoint_val {space : Space.{0, u} realSource} (weight : ENNReal) (point : space.Carrier) :
    (weightedPoint space (weight, point)).val = Measure.smul weight (Measure.dirac space.toMeasurable point) := by
  change (scale space (weight, pure space point)).val = _
  rw [scale_val, pure_val]

/-- Reweighting morphism transforming an s-finite law by an extended-nonnegative density. -/
@[expose] noncomputable def weight {space : Space.{0, u} realSource} (density : Hom space weightSpace) :
    Hom (object space) (object space) :=
  extend (Hom.comp (weightedPoint space) (Space.pair density (Hom.identity space)))

theorem weight_apply {space : Space.{0, u} realSource} (density : Hom space weightSpace) (law : Law space) :
    weight density law = bind law
      (Hom.comp (weightedPoint space) (Space.pair density (Hom.identity space))) := rfl

/-- Higher-order morphism reweighting a law by a function-space density. -/
@[expose] noncomputable def weightValue (space : Space.{0, u} realSource) :
    Hom (Space.product (Space.exponential space weightSpace) (object space)) (object space) :=
  let continuation := Hom.comp (weightedPoint space)
    (Space.pair (Space.evaluate space weightSpace) (Space.second (Space.exponential space weightSpace) space))
  Hom.comp (bindValue space space) (Space.productMap (Space.curry continuation) (Hom.identity (object space)))

theorem weightValue_apply {space : Space.{0, u} realSource}
    (density : Hom space weightSpace) (law : Law space) :
    weightValue space (density, law) = weight density law := by
  unfold weightValue
  change bindValue space space (_, law) = _
  rw [bindValue_apply]
  change bind law _ = bind law _
  apply congrArg (bind law)
  apply Hom.ext
  intro point
  rfl

/-- Reweighting an s-finite law agrees with measure density modification. -/
theorem weight_val {space : Space.{0, u} realSource} (density : Hom space weightSpace) (law : Law space) :
    (weight density law).val = law.val.withDensity density := by
  classical
  apply Measure.ext
  intro region measurable
  rw [weight_apply, bind_val, Measure.bind_apply _ _ @measurable,
    Measure.withDensity_apply _ _ @measurable]
  have equal : (fun point => toKernel
      (Hom.comp (weightedPoint space) (Space.pair density (Hom.identity space))) point region) =
        ennrealIndicator region density := by
    funext point
    change (weightedPoint space (density point, point)).val region = _
    rw [weightedPoint_val, Measure.smul_apply_measurable _ _ @measurable]
    by_cases member : region point
    · rw [Measure.dirac_apply_of_mem _ _ @measurable member, ENNReal.mulOne]
      simp only [ennrealIndicator, ennrealPiecewise, if_pos member]
    · rw [Measure.dirac_apply_of_not_mem _ _ @measurable member, ENNReal.mulZero]
      simp only [ennrealIndicator, ennrealPiecewise, if_neg member]
  rw [equal]
  exact lintegral_indicator law.val region @measurable density

theorem weight_const {space : Space.{0, u} realSource} (factor : ENNReal) (law : Law space) :
    weight (Hom.constant space weightSpace factor) law = scale space (factor, law) := by
  apply Law.ext
  rw [weight_val, scale_val]
  exact law.val.withDensity_const factor

@[simp] theorem weight_one (space : Space.{0, u} realSource) :
    weight (Hom.constant space weightSpace ENNReal.one) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  rw [weight_const, scale_one]
  rfl

@[simp] theorem weight_zero (space : Space.{0, u} realSource) :
    weight (Hom.constant space weightSpace ENNReal.zero) =
      Hom.constant (object space) (object space) (zero space) := by
  apply Hom.ext
  intro law
  rw [weight_const, scale_zero]
  rfl

@[simp] theorem weight_zero_law {space : Space.{0, u} realSource} (density : Hom space weightSpace) :
    weight density (zero space) = zero space := by
  rw [weight_apply, zero_bind]

theorem weight_pure {space : Space.{0, u} realSource} (density : Hom space weightSpace)
    (point : space.Carrier) :
    weight density (pure space point) = scale space (density point, pure space point) := by
  rw [weight_apply, pure_bind]
  rfl

theorem mass_weight {space : Space.{0, u} realSource} (density : Hom space weightSpace) (law : Law space) :
    mass space (weight density law) = lintegral law.val density := by
  rw [mass_apply, weight_val,
    Measure.withDensity_apply _ _ (by exact space.toMeasurable.univ), Measure.restrict_univ]

theorem weight_weight {space : Space.{0, u} realSource}
    (first second : Hom space weightSpace) (law : Law space) :
    weight second (weight first law) = weight (Hom.comp weightMul (Space.pair first second)) law := by
  apply Law.ext
  rw [weight_val, weight_val, weight_val,
    Measure.withDensity_withDensity _ (weight_measurable first) (weight_measurable second)]
  rfl

theorem weight_comm {space : Space.{0, u} realSource} (first second : Hom space weightSpace) :
    Hom.comp (weight first) (weight second) = Hom.comp (weight second) (weight first) := by
  apply Hom.ext
  intro law
  change weight first (weight second law) = weight second (weight first law)
  rw [weight_weight, weight_weight]
  apply congrArg (fun density => weight density law)
  apply Hom.ext
  intro point
  exact ENNReal.mulComm (second point) (first point)

theorem weight_natural {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (function : Hom domain codomain) (density : Hom codomain weightSpace) (law : Law domain) :
    map function (weight (Hom.comp density function) law) = weight density (map function law) := by
  rw [weight_apply, map_bind, weight_apply, bind_map]
  apply congrArg (bind law)
  apply Hom.ext
  intro point
  change map function (scale domain (density (function point), pure domain point)) =
    scale codomain (density (function point), pure codomain (function point))
  rw [scale_natural, map_pure]

theorem weight_bind {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (density : Hom codomain weightSpace) (law : Law domain) (kernel : Hom domain (object codomain)) :
    weight density (bind law kernel) = bind law (Hom.comp (weight density) kernel) := by
  rw [weight_apply, bind_assoc]
  rfl

theorem bind_weight {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (density : Hom domain weightSpace) (law : Law domain) (kernel : Hom domain (object codomain)) :
    bind (weight density law) kernel = bind law (Hom.comp (scale codomain) (Space.pair density kernel)) := by
  rw [weight_apply, bind_assoc]
  apply congrArg (bind law)
  apply Hom.ext
  intro point
  change bind (scale domain (density point, pure domain point)) kernel =
    scale codomain (density point, kernel point)
  rw [← scale_bind, pure_bind]

/-- Global s-finite kernel certificate for the deterministic weighted-point kernel. -/
noncomputable def toKernel_weightedPoint_sfinite (space : Space.{0, u} realSource) :
    Kernel.IsSFinite (toKernel (weightedPoint space)) := by
  let parameter := Space.product weightSpace space
  let projection := Space.second weightSpace space
  let base := Kernel.deterministic projection projection.toMeasurable
  let finite := Kernel.IsSFinite.deterministic projection projection.toMeasurable
  let density : parameter.Carrier → space.Carrier → ENNReal := fun input _ => input.1
  have measurable : ENNRealMeasurable
      (Foundations.Measure.Space.product parameter.toMeasurable space.toMeasurable)
      (fun pair => density pair.1 pair.2) :=
    (weight_measurable (Space.first weightSpace space)).comp
      (Foundations.Measure.Space.first_measurable parameter.toMeasurable space.toMeasurable)
  have equal : base.withDensity finite density measurable = toKernel (weightedPoint space) := by
    apply Kernel.ext
    intro input
    change (Measure.dirac space.toMeasurable input.2).withDensity (fun _ => input.1) =
      (weightedPoint space input).val
    rw [Measure.withDensity_const]
    exact (weightedPoint_val input.1 input.2).symm
  exact equal ▸ finite.withDensity density measurable

end

end Foundations.QuasiBorel.SFinite
