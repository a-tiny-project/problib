import Problib.Analysis.Real.Dominated
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Kernel.Measurable

set_option autoImplicit false

/-! Certified signed integrals under point masses, pushforwards, and binds.

A program's law is assembled from point masses, pushforwards along measurable
maps, and kernel binds, and an estimator's mean is a certified finite signed
integral. An estimator proof therefore moves `HasRealIntegral` through each of
the three constructions. The point-mass and pushforward rules need only
measurability. The bind rule is Fubini for a signed integrand: the size of the
integrand must be integrable under the iterated measure, every fiber must carry
a certified integral, and then the fiber integrals are integrable with the same
total as the bind. -/

namespace Problib.Inference.Derivative.Continuous

open Problib.Real Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real
open Problib.Analysis.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- The positive part of a measurable real integrand, embedded, is measurable. -/
private theorem positiveMeasurable {space : Space α} {integrand : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand) :
    ENNRealMeasurable space (fun x => ENNReal.ofReal (integrand x)) :=
  ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable measurable

/-- The negative part of a measurable real integrand, embedded, is measurable. -/
private theorem negativeMeasurable {space : Space α} {integrand : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand) :
    ENNRealMeasurable space (fun x => ENNReal.ofReal (neg (integrand x))) :=
  ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
    (MeasurableMap.comp neg_measurable measurable)

/-- A point mass integrates a measurable integrand to its value at the point. -/
theorem hasRealIntegral_dirac (space : Space α) (point : α)
    {integrand : α → selection.Carrier}
    (measurable : MeasurableMap space borel integrand) :
    HasRealIntegral (Measure.dirac space point) integrand (integrand point) :=
  ⟨{ positive := fun x => NNReal.ofReal (integrand x)
     negative := fun x => NNReal.ofReal (neg (integrand x))
     positive_measurable := positiveMeasurable measurable
     negative_measurable := negativeMeasurable measurable
     decomposition := fun x => IntegralParts.scalar_decomposition (integrand x)
     positiveMass := NNReal.ofReal (integrand point)
     negativeMass := NNReal.ofReal (neg (integrand point))
     positive_integral := lintegral_dirac space point (positiveMeasurable measurable)
     negative_integral := lintegral_dirac space point (negativeMeasurable measurable) },
    (IntegralParts.scalar_decomposition (integrand point)).symm⟩

/-- An integral under a pushforward is the integral of the composite under the
source measure. The certified parts compose with the map, so the integrand
needs no measurability of its own. -/
theorem hasRealIntegral_of_map (measure : Measure source) (before : α → β)
    (beforeMeasurable : MeasurableMap source target before)
    {integrand : β → selection.Carrier} {value : selection.Carrier}
    (integral : HasRealIntegral (measure.map before beforeMeasurable) integrand value) :
    HasRealIntegral measure (fun x => integrand (before x)) value := by
  obtain ⟨parts, same⟩ := integral
  exact ⟨{ positive := fun x => parts.positive (before x)
           negative := fun x => parts.negative (before x)
           positive_measurable :=
             ENNRealMeasurable.comp (map := fun y => ENNReal.finite (parts.positive y))
               parts.positive_measurable beforeMeasurable
           negative_measurable :=
             ENNRealMeasurable.comp (map := fun y => ENNReal.finite (parts.negative y))
               parts.negative_measurable beforeMeasurable
           decomposition := fun x => parts.decomposition (before x)
           positiveMass := parts.positiveMass
           negativeMass := parts.negativeMass
           positive_integral :=
             (lintegral_map measure before beforeMeasurable
               parts.positive_measurable).symm.trans parts.positive_integral
           negative_integral :=
             (lintegral_map measure before beforeMeasurable
               parts.negative_measurable).symm.trans parts.negative_integral }, same⟩

/-- A measurable integrand whose composite with a map has a certified integral
has the same integral under the pushforward. The composite's parts bound the
size of the integrand under the pushforward, and the canonical parts there
compose back to a certificate that uniqueness identifies. -/
theorem hasRealIntegral_map (measure : Measure source) (before : α → β)
    (beforeMeasurable : MeasurableMap source target before)
    {integrand : β → selection.Carrier} {value : selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (integral : HasRealIntegral measure (fun x => integrand (before x)) value) :
    HasRealIntegral (measure.map before beforeMeasurable) integrand value := by
  obtain ⟨parts, same⟩ := integral
  have sizeFinite : ENNReal.Finite (lintegral (measure.map before beforeMeasurable)
      (fun y => ENNReal.ofReal (abs (integrand y)))) := by
    rw [lintegral_map measure before beforeMeasurable (abs_measurable measurable)]
    exact parts.lintegral_abs_finite
  let pushed := IntegralParts.ofSizeFinite measurable sizeFinite
  refine ⟨pushed, ?_⟩
  have pulled := hasRealIntegral_of_map measure before beforeMeasurable ⟨pushed, rfl⟩
  exact HasRealIntegral.unique pulled ⟨parts, same⟩

/-- Pushforward and composition agree on every certified value of a measurable
integrand. -/
theorem hasRealIntegral_map_iff (measure : Measure source) (before : α → β)
    (beforeMeasurable : MeasurableMap source target before)
    {integrand : β → selection.Carrier} {value : selection.Carrier}
    (measurable : MeasurableMap target borel integrand) :
    HasRealIntegral (measure.map before beforeMeasurable) integrand value ↔
      HasRealIntegral measure (fun x => integrand (before x)) value :=
  ⟨hasRealIntegral_of_map measure before beforeMeasurable,
    hasRealIntegral_map measure before beforeMeasurable measurable⟩

/-- Fubini for certified signed integrals under a kernel bind. The size of the
integrand must be integrable under the iterated measure, and every fiber must
carry a certified integral. Then the fiber integrals are integrable, and their
integral and the integral under the bind are one value.

The proof never subtracts infinite quantities. The fiber integrals of the two
canonical parts are finite at every input, because each fiber is certified.
They are measurable in the input, and they integrate to the two canonical
parts of the bind, so they certify the fiber integrals with the bind's masses. -/
theorem mixture (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier} {fiber : α → selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral measure (fun x =>
      lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))))
    (fibers : ∀ x, HasRealIntegral (kernel x) integrand (fiber x)) :
    ∃ value, HasRealIntegral (measure.bind kernel) integrand value ∧
      HasRealIntegral measure fiber value := by
  classical
  have jointFinite : ENNReal.Finite (lintegral (measure.bind kernel)
      (fun y => ENNReal.ofReal (abs (integrand y)))) := by
    rw [Measure.lintegral_bind measure kernel (abs_measurable measurable)]
    exact sizeFinite
  let joint := IntegralParts.ofSizeFinite measurable jointFinite
  let conditional := fun x => IntegralParts.ofSizeFinite measurable
    (Classical.choose (fibers x)).lintegral_abs_finite
  have conditionalValue : ∀ x, (conditional x).value = fiber x := fun x =>
    ((conditional x).unique (Classical.choose (fibers x))).trans
      (Classical.choose_spec (fibers x))
  have positiveFiber : (fun x => ENNReal.finite (conditional x).positiveMass) =
      fun x => lintegral (kernel x) (fun y => ENNReal.ofReal (integrand y)) :=
    funext fun x => (conditional x).positive_integral.symm
  have negativeFiber : (fun x => ENNReal.finite (conditional x).negativeMass) =
      fun x => lintegral (kernel x) (fun y => ENNReal.ofReal (neg (integrand y))) :=
    funext fun x => (conditional x).negative_integral.symm
  have positiveFiberMeasurable :
      ENNRealMeasurable source (fun x => ENNReal.finite (conditional x).positiveMass) := by
    rw [positiveFiber]
    exact kernel.lintegral_measurable (positiveMeasurable measurable)
  have negativeFiberMeasurable :
      ENNRealMeasurable source (fun x => ENNReal.finite (conditional x).negativeMass) := by
    rw [negativeFiber]
    exact kernel.lintegral_measurable (negativeMeasurable measurable)
  have positiveTotal :
      lintegral measure (fun x => ENNReal.finite (conditional x).positiveMass) =
        ENNReal.finite joint.positiveMass := by
    rw [positiveFiber, ← Measure.lintegral_bind measure kernel (positiveMeasurable measurable)]
    exact joint.positive_integral
  have negativeTotal :
      lintegral measure (fun x => ENNReal.finite (conditional x).negativeMass) =
        ENNReal.finite joint.negativeMass := by
    rw [negativeFiber, ← Measure.lintegral_bind measure kernel (negativeMeasurable measurable)]
    exact joint.negative_integral
  let mixed : IntegralParts measure fiber :=
    { positive := fun x => (conditional x).positiveMass
      negative := fun x => (conditional x).negativeMass
      positive_measurable := positiveFiberMeasurable
      negative_measurable := negativeFiberMeasurable
      decomposition := fun x => (conditionalValue x).symm
      positiveMass := joint.positiveMass
      negativeMass := joint.negativeMass
      positive_integral := positiveTotal
      negative_integral := negativeTotal }
  exact ⟨joint.value, ⟨joint, rfl⟩, ⟨mixed, rfl⟩⟩

/-- The bind integrates a signed integrand to the integral of its fiber
integrals, given the iterated size bound. -/
theorem hasRealIntegral_bind (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier} {fiber : α → selection.Carrier}
    {value : selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral measure (fun x =>
      lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))))
    (fibers : ∀ x, HasRealIntegral (kernel x) integrand (fiber x))
    (outer : HasRealIntegral measure fiber value) :
    HasRealIntegral (measure.bind kernel) integrand value := by
  obtain ⟨mean, joint, mixed⟩ := mixture measure kernel measurable sizeFinite fibers
  rwa [HasRealIntegral.unique mixed outer] at joint

/-- The iterated size bound is the size bound under the bind. -/
theorem sizeFinite_bind_iff (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier}
    (measurable : MeasurableMap target borel integrand) :
    ENNReal.Finite (lintegral (measure.bind kernel)
        (fun y => ENNReal.ofReal (abs (integrand y)))) ↔
      ENNReal.Finite (lintegral measure (fun x =>
        lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))) := by
  rw [Measure.lintegral_bind measure kernel (abs_measurable measurable)]

end Problib.Inference.Derivative.Continuous
