module

public import Problib.Measure.Kernel.Density.Conditional
import Problib.Measure.Integral.Density.Algebra
import Problib.Measure.Integral.Density.Change

set_option autoImplicit false

/-! # Normalized families

A parameterized family of laws is often given by an unnormalized weight
`w(θ, x)` against a fixed reference. Its normalizer is `Z(θ) = ∫ w(θ, x)`, and
its law at `θ` is the weighted reference divided by `Z(θ)`. A
`NormalizedFamily` packages the weight, jointly measurable in the parameter and
the value, with an s-finite reference and a measurable fallback map. Its kernel
normalizes the weight where it can and is the Dirac kernel of the fallback map
elsewhere, so it is measurable in the parameter by construction. Where the
weight is normalizable, the law is the conditional kernel of the weight
(`law_eq_densityConditional`).

Wherever `Z(θ)` is finite and nonzero, the law is the normalization of the
weighted reference (`law_eq_normalize`), with density `w/Z`
(`law_eq_withDensity`, `law_integral`). A family names a closed-form density
`c·w` by showing `c·Z(θ) = 1` (`law_eq_of_scale`).

A factor that tilts the weight at `θ` into `s` times the weight at `θ'` has
integral `s·Z(θ')/Z(θ)` under the law at `θ`
(`normalizer_mul_lintegral_law`), the normalizer ratio behind closed-form
evidence. An infinite `Z(θ')` makes that integral infinite
(`lintegral_law_eq_top`). Wherever `Z(θ)` is zero or
infinite, the law is the Dirac measure at the fallback of that parameter
(`law_eq_dirac`), so a family can place its degenerate limit there. Every law is
a probability measure. -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

/-- A family of laws given by a jointly measurable weight against an s-finite
reference. The fallback map gives the law's point mass wherever the weight has
no normalization. -/
public structure NormalizedFamily {alpha : Type u} {beta : Type v}
    (source : Space alpha) (target : Space beta) where
  reference : Measure target
  referenceFinite : Measure.SFinite reference
  weight : alpha → beta → ENNReal
  weight_measurable : ENNRealMeasurable (Space.product source target)
    (fun pair => weight pair.1 pair.2)
  fallback : alpha → beta
  fallback_measurable : MeasurableMap source target fallback

namespace NormalizedFamily

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}
  (family : NormalizedFamily source target)

/-- The normalizer `Z(θ)`: the integral of the weight at `θ` against the
reference. -/
@[expose] public noncomputable def normalizer (parameter : alpha) : ENNReal :=
  densityMass family.reference family.weight parameter

/-- The normalized density `w/Z`. -/
@[expose] public noncomputable def density (parameter : alpha) (value : beta) : ENNReal :=
  normalizedDensity family.reference family.weight parameter value

/-- The family's kernel: the normalized weight where it is normalizable, and the
Dirac kernel of the fallback map elsewhere. -/
@[expose] public noncomputable def kernel : Kernel source target :=
  piecewise (fun input => Measure.IsNormalizable
      (densityFiber family.reference family.weight input))
    (normalizableFiber_measurable family.referenceFinite family.weight_measurable)
    ((Kernel.const source family.reference).withDensity
      (IsSFinite.const source family.referenceFinite)
      (normalizedDensity family.reference family.weight)
      (normalizedDensity_measurable family.referenceFinite family.weight_measurable))
    (deterministic family.fallback family.fallback_measurable)

/-- The family's law at one parameter. -/
@[expose] public noncomputable def law (parameter : alpha) : Measure target :=
  family.kernel parameter

public theorem kernel_apply (parameter : alpha) : family.kernel parameter = family.law parameter :=
  rfl

public theorem normalizer_eq (parameter : alpha) :
    family.normalizer parameter = lintegral family.reference (family.weight parameter) :=
  rfl

public theorem normalizer_measurable : ENNRealMeasurable source family.normalizer :=
  densityMass_measurable family.referenceFinite family.weight_measurable

public theorem density_measurable :
    ENNRealMeasurable (Space.product source target) (fun pair => family.density pair.1 pair.2) :=
  normalizedDensity_measurable family.referenceFinite family.weight_measurable

public theorem weight_measurable_slice (parameter : alpha) :
    ENNRealMeasurable target (family.weight parameter) :=
  jointly_measurable_slice family.weight_measurable parameter

public theorem density_measurable_slice (parameter : alpha) :
    ENNRealMeasurable target (family.density parameter) :=
  jointly_measurable_slice family.density_measurable parameter

/-- The weighted reference is normalizable exactly when the normalizer is finite
and nonzero. -/
public theorem isNormalizable_iff (parameter : alpha) :
    Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)) ↔
      ENNReal.Finite (family.normalizer parameter) ∧
        family.normalizer parameter ≠ ENNReal.zero :=
  isNormalizable_densityFiber_iff family.reference family.weight parameter

/-- Where the weight is normalizable, the law is the conditional kernel of the
weight at that parameter, whatever its fallback point. -/
public theorem law_eq_densityConditional {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)))
    (point : beta) :
    family.law parameter = densityConditional family.reference family.referenceFinite
      family.weight family.weight_measurable point parameter := by
  unfold law kernel densityConditional
  rw [piecewise_apply_of_mem _ _ _ _ parameter defined,
    piecewise_apply_of_mem _ _ _ _ parameter defined]

/-- Where the weight is normalizable, the law is its normalization. -/
public theorem law_eq_normalize {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))) :
    family.law parameter =
      Measure.normalize (family.reference.withDensity (family.weight parameter)) defined :=
  (family.law_eq_densityConditional defined (family.fallback parameter)).trans
    (densityConditional_eq_normalize family.reference family.referenceFinite
      family.weight_measurable (family.fallback parameter) parameter defined)

/-- Where the weight is not normalizable, the law is the point mass at the
fallback of that parameter. -/
public theorem law_eq_dirac {parameter : alpha}
    (undefined :
      ¬Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))) :
    family.law parameter = Measure.dirac target (family.fallback parameter) := by
  unfold law kernel
  rw [piecewise_apply_of_not_mem _ _ _ _ parameter undefined, deterministic_apply]

/-- Every law of the family is a probability measure. -/
public theorem law_isProbability (parameter : alpha) :
    Measure.IsProbability (family.law parameter) := by
  classical
  by_cases defined :
      Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))
  · rw [family.law_eq_normalize defined]
    exact Measure.normalize_isProbability _ defined
  · rw [family.law_eq_dirac defined]
    exact Measure.IsProbability.dirac target _

/-- An infinite normalizer sends the law to the fallback. -/
public theorem law_eq_dirac_of_top {parameter : alpha}
    (infinite : family.normalizer parameter = ENNReal.top) :
    family.law parameter = Measure.dirac target (family.fallback parameter) :=
  family.law_eq_dirac (fun defined =>
    ENNReal.finite_iff_ne_top.mp ((family.isNormalizable_iff parameter).mp defined).1 infinite)

/-- A zero normalizer sends the law to the fallback. -/
public theorem law_eq_dirac_of_zero {parameter : alpha}
    (vanishing : family.normalizer parameter = ENNReal.zero) :
    family.law parameter = Measure.dirac target (family.fallback parameter) :=
  family.law_eq_dirac (fun defined =>
    ((family.isNormalizable_iff parameter).mp defined).2 vanishing)

/-- Where the weight is normalizable, the law has density `w/Z` against the
reference. -/
public theorem law_eq_withDensity {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))) :
    family.law parameter = family.reference.withDensity (family.density parameter) := by
  unfold law kernel
  rw [piecewise_apply_of_mem _ _ _ _ parameter defined, withDensity_apply, Kernel.const_apply]
  rfl

/-- Where the weight is normalizable, integration against the law is
integration against the reference weighted by `w/Z`. -/
public theorem law_integral {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)))
    {integrand : beta → ENNReal} (measurable : ENNRealMeasurable target integrand) :
    lintegral (family.law parameter) integrand = lintegral family.reference
      (fun value => ENNReal.mul (family.density parameter value) (integrand value)) := by
  rw [family.law_eq_withDensity defined]
  exact Problib.Measure.lintegral_withDensity family.reference
    (family.density_measurable_slice parameter) measurable

/-- Where the weight is normalizable, `w/Z` integrates to one. -/
public theorem density_integral {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))) :
    lintegral family.reference (family.density parameter) = ENNReal.one := by
  have total := (family.law_isProbability parameter).univ_eq_one
  rwa [family.law_eq_withDensity defined,
    family.reference.withDensity_apply _ target.univ, family.reference.restrict_univ] at total

/-- A scale `c` with `c·Z(θ) = 1` makes `Z(θ)` finite and nonzero. -/
public theorem isNormalizable_of_scale {parameter : alpha} {scale : ENNReal}
    (cancel : ENNReal.mul scale (family.normalizer parameter) = ENNReal.one) :
    Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)) := by
  have one_ne_top : ENNReal.one ≠ ENNReal.top :=
    ENNReal.finite_iff_ne_top.mp (show ENNReal.Finite ENNReal.one from True.intro)
  refine (family.isNormalizable_iff parameter).mpr ⟨ENNReal.finite_iff_ne_top.mpr ?_, ?_⟩
  · intro infinite
    rw [infinite] at cancel
    by_cases vanishing : scale = ENNReal.zero
    · rw [vanishing, ENNReal.zero_mul] at cancel
      exact ENNReal.one_ne_zero cancel.symm
    · rw [ENNReal.mul_top_of_ne_zero vanishing] at cancel
      exact one_ne_top cancel.symm
  · intro vanishing
    rw [vanishing, ENNReal.mul_zero] at cancel
    exact ENNReal.one_ne_zero cancel.symm

/-- A closed-form density `c·w` with `c·Z(θ) = 1` is the law's density. -/
public theorem law_eq_of_scale {parameter : alpha} {scale : ENNReal}
    (cancel : ENNReal.mul scale (family.normalizer parameter) = ENNReal.one)
    {closed : beta → ENNReal}
    (factor : ∀ value, closed value = ENNReal.mul scale (family.weight parameter value)) :
    family.law parameter = family.reference.withDensity closed := by
  have defined := family.isNormalizable_of_scale cancel
  have closedEq : closed = fun value => ENNReal.mul scale (family.weight parameter value) :=
    funext factor
  rw [family.law_eq_normalize defined]
  apply Measure.normalize_eq_of_smul_eq
  rw [family.reference.withDensity_apply _ target.univ, family.reference.restrict_univ,
    closedEq, ← Measure.smul_withDensity _ _ (family.weight_measurable_slice parameter),
    Measure.smul_smul]
  show Measure.smul (ENNReal.mul (family.normalizer parameter) scale)
      (family.reference.withDensity (family.weight parameter)) = _
  rw [ENNReal.mul_comm, cancel, Measure.one_smul]

/-- Where the weight is normalizable, the normalizer times the law is the
weighted reference. -/
public theorem normalizer_smul_law {parameter : alpha}
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter))) :
    Measure.smul (family.normalizer parameter) (family.law parameter) =
      family.reference.withDensity (family.weight parameter) := by
  obtain ⟨mass, total⟩ := ENNReal.exists_finite_of_finite defined.finite.univ_finite
  have nonzero : mass ≠ NNReal.zero :=
    fun vanishing => defined.nonzero (total.trans (congrArg ENNReal.finite vanishing))
  have massEq : family.normalizer parameter = ENNReal.finite mass := by
    rw [← total, family.reference.withDensity_apply _ target.univ, family.reference.restrict_univ]
    rfl
  rw [family.law_eq_normalize defined, Measure.normalize_eq_of_total_eq _ defined total,
    Measure.smul_smul, massEq, ENNReal.finite_mul_finite, NNReal.mul_div_cancel _ nonzero]
  exact Measure.one_smul _

/-- The normalizer ratio. A factor with `w(θ, x)·f(x) = s·w(θ', x)` has
`Z(θ)·∫ f d(law θ) = s·Z(θ')` wherever the weight at `θ` is normalizable. -/
public theorem normalizer_mul_lintegral_law {parameter updated : alpha} {scale : ENNReal}
    {factor : beta → ENNReal} (measurable : ENNRealMeasurable target factor)
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)))
    (tilt : ∀ value, ENNReal.mul (family.weight parameter value) (factor value) =
      ENNReal.mul scale (family.weight updated value)) :
    ENNReal.mul (family.normalizer parameter) (lintegral (family.law parameter) factor) =
      ENNReal.mul scale (family.normalizer updated) := by
  rw [← lintegral_smul_measure, family.normalizer_smul_law defined,
    Problib.Measure.lintegral_withDensity family.reference
      (family.weight_measurable_slice parameter) measurable]
  simp only [tilt]
  exact lintegral_smul _ _ (family.weight_measurable_slice updated)

/-- The normalizer ratio against a closed-form reciprocal: with `c·Z(θ) = 1`,
the integral is `c·s·Z(θ')`. -/
public theorem lintegral_law_of_scale {parameter updated : alpha} {reciprocal scale : ENNReal}
    {factor : beta → ENNReal} (measurable : ENNRealMeasurable target factor)
    (cancel : ENNReal.mul reciprocal (family.normalizer parameter) = ENNReal.one)
    (tilt : ∀ value, ENNReal.mul (family.weight parameter value) (factor value) =
      ENNReal.mul scale (family.weight updated value)) :
    lintegral (family.law parameter) factor =
      ENNReal.mul reciprocal (ENNReal.mul scale (family.normalizer updated)) := by
  rw [← family.normalizer_mul_lintegral_law measurable (family.isNormalizable_of_scale cancel)
    tilt, ← ENNReal.mul_assoc, cancel, ENNReal.one_mul]

/-- An infinite normalizer at `θ'` makes the tilted integral infinite: the
ratio `s·Z(θ')/Z(θ)` is then no density. -/
public theorem lintegral_law_eq_top {parameter updated : alpha} {scale : ENNReal}
    {factor : beta → ENNReal} (measurable : ENNRealMeasurable target factor)
    (defined : Measure.IsNormalizable (family.reference.withDensity (family.weight parameter)))
    (tilt : ∀ value, ENNReal.mul (family.weight parameter value) (factor value) =
      ENNReal.mul scale (family.weight updated value))
    (scaleNonzero : scale ≠ ENNReal.zero) (infinite : family.normalizer updated = ENNReal.top) :
    lintegral (family.law parameter) factor = ENNReal.top := by
  have ratio := family.normalizer_mul_lintegral_law measurable defined tilt
  rw [infinite, ENNReal.mul_top_of_ne_zero scaleNonzero] at ratio
  apply Classical.byContradiction
  intro finite
  have bounded := ENNReal.mul_finite ((family.isNormalizable_iff parameter).mp defined).1
    (ENNReal.finite_iff_ne_top.mpr finite)
  rw [ratio] at bounded
  exact ENNReal.finite_iff_ne_top.mp bounded rfl

end NormalizedFamily

end Problib.Measure.Kernel
