import Problib.Analysis.Real.Dominated
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Real.Nonnegative
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Integral.Lebesgue.Markov

set_option autoImplicit false

/-! Certified signed integrals under point masses, pushforwards, and binds.

A program's law is assembled from point masses, pushforwards along measurable
maps, and kernel binds, and an estimator's mean is a certified finite signed
integral. An estimator proof therefore moves `HasRealIntegral` through each of
the three constructions. The point-mass and pushforward rules need only
measurability. The bind rule is Fubini for a signed integrand: when the size of
the integrand is integrable under the iterated measure, almost every fiber
carries a certified integral, and the fiber integrals are integrable with the
same total as the bind. -/

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

/-- The fiber integral of a part of a readout, read as a real. An infinite fiber
integral reads as zero, which matters only on a null set of inputs. -/
private noncomputable def partMean (kernel : Kernel source target)
    (part : β → selection.Carrier) (x : α) : selection.Carrier :=
  ENNReal.toReal (lintegral (kernel x) (fun y => ENNReal.ofReal (part y)))

/-- A part's fiber readout integrates to the part's mass under the bind, when
its fiber integrals are finite almost everywhere. The readout is measurable
because kernel lower integrals are, and it agrees with the fiber integral
wherever that is finite. -/
private theorem hasRealIntegral_partMean (measure : Measure source)
    (kernel : Kernel source target) {part : β → selection.Carrier} {mass : NNReal}
    (measurable : MeasurableMap target borel part)
    (finiteFibers : measure.AE fun x =>
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (part y))))
    (total : lintegral (measure.bind kernel) (fun y => ENNReal.ofReal (part y)) =
      ENNReal.finite mass) :
    HasRealIntegral measure (partMean kernel part) mass.toReal := by
  have fiberMeasurable := kernel.lintegral_measurable (positiveMeasurable measurable)
  refine HasRealIntegral.of_lintegral_ofReal
    (MeasurableMap.comp toReal_measurable fiberMeasurable.measurableMap)
    (fun _ => ENNReal.toReal_nonnegative _) mass.property ?_
  rw [show ENNReal.ofReal mass.toReal = ENNReal.finite mass from
      ENNReal.ofReal_toReal_finite mass, ← total,
    Measure.lintegral_bind measure kernel (positiveMeasurable measurable)]
  exact lintegral_congr_ae (finiteFibers.mono fun _ finite => ENNReal.ofReal_toReal finite)

/-- A certified fiber has finite part integrals, and their readouts recover its
value. -/
private theorem fiber_readout (kernel : Kernel source target)
    {integrand : β → selection.Carrier} {x : α} {mean : selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (certified : HasRealIntegral (kernel x) integrand mean) :
    ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (integrand y))) ∧
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (neg (integrand y)))) ∧
      sub (partMean kernel integrand x) (partMean kernel (fun y => neg (integrand y)) x) =
        mean := by
  obtain ⟨parts, same⟩ := certified
  let conditional := IntegralParts.ofSizeFinite measurable parts.lintegral_abs_finite
  have positive : lintegral (kernel x) (fun y => ENNReal.ofReal (integrand y)) =
      ENNReal.finite conditional.positiveMass := conditional.positive_integral
  have negative : lintegral (kernel x) (fun y => ENNReal.ofReal (neg (integrand y))) =
      ENNReal.finite conditional.negativeMass := conditional.negative_integral
  refine ⟨by rw [positive]; exact True.intro, by rw [negative]; exact True.intro, ?_⟩
  unfold partMean
  rw [positive, negative]
  exact (conditional.unique parts).trans same

/-- The conditional mean, read from the fibers' part integrals, and the bind
have one integral. The size bound makes the bind integrable, and the part
readouts integrate to the bind's two part masses when the fibers' part
integrals are finite almost everywhere. -/
private theorem conditional_mean (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral measure (fun x =>
      lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))))
    (finiteFibers : measure.AE fun x =>
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (integrand y))) ∧
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (neg (integrand y))))) :
    ∃ value, HasRealIntegral (measure.bind kernel) integrand value ∧
      HasRealIntegral measure (fun x =>
        sub (partMean kernel integrand x) (partMean kernel (fun y => neg (integrand y)) x))
        value := by
  have jointFinite : ENNReal.Finite (lintegral (measure.bind kernel)
      (fun y => ENNReal.ofReal (abs (integrand y)))) := by
    rw [Measure.lintegral_bind measure kernel (abs_measurable measurable)]
    exact sizeFinite
  let joint := IntegralParts.ofSizeFinite measurable jointFinite
  exact ⟨joint.value, ⟨joint, rfl⟩,
    (hasRealIntegral_partMean measure kernel measurable
      (finiteFibers.mono fun _ holds => holds.1) joint.positive_integral).sub
    (hasRealIntegral_partMean measure kernel (MeasurableMap.comp neg_measurable measurable)
      (finiteFibers.mono fun _ holds => holds.2) joint.negative_integral)⟩

/-- Fubini for certified signed integrals under a kernel bind, with every fiber
certified. The size of the integrand must be integrable under the iterated
measure. Then the fiber integrals are integrable, and their integral and the
integral under the bind are one value. The fibers are certified everywhere
because the conclusion certifies the fiber integrals themselves, and a
certificate reads its integrand at every input. -/
theorem mixture (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier} {fiber : α → selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral measure (fun x =>
      lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))))
    (fibers : ∀ x, HasRealIntegral (kernel x) integrand (fiber x)) :
    ∃ value, HasRealIntegral (measure.bind kernel) integrand value ∧
      HasRealIntegral measure fiber value := by
  obtain ⟨value, joint, conditional⟩ := conditional_mean measure kernel measurable sizeFinite
    (Measure.ae_of_forall fun x =>
      let readout := fiber_readout kernel measurable (fibers x)
      ⟨readout.1, readout.2.1⟩)
  exact ⟨value, joint,
    conditional.congr fun x => (fiber_readout kernel measurable (fibers x)).2.2⟩

/-- Fubini for certified signed integrals under a kernel bind. The size of the
integrand must be integrable under the iterated measure, and almost every fiber
must carry a certified integral. Then the fiber integrals and the bind have one
integral.

Joint integrability is not implied by the fibers and the outer integral: fibers
of mean zero can cancel under an infinite outer mass (`Cancelling`). Fibers on
a null set of inputs may have no integral at all (`NullFiber`).

The proof never subtracts infinite quantities. It reads the fiber integrals of
the two canonical parts as reals. Both readouts are measurable, they are finite
wherever a fiber is certified, and they integrate to the bind's two part
masses. Their difference is the fiber integral almost everywhere, so it carries
the bind's value to `fiber`. -/
theorem hasRealIntegral_bind (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier} {fiber : α → selection.Carrier}
    {value : selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral measure (fun x =>
      lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))))
    (fibers : measure.AE fun x => HasRealIntegral (kernel x) integrand (fiber x))
    (outer : HasRealIntegral measure fiber value) :
    HasRealIntegral (measure.bind kernel) integrand value := by
  have readout : measure.AE fun x =>
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (integrand y))) ∧
      ENNReal.Finite (lintegral (kernel x) (fun y => ENNReal.ofReal (neg (integrand y)))) ∧
      sub (partMean kernel integrand x) (partMean kernel (fun y => neg (integrand y)) x) =
        fiber x :=
    fibers.mono fun _ certified => fiber_readout kernel measurable certified
  obtain ⟨mean, joint, conditional⟩ := conditional_mean measure kernel measurable sizeFinite
    (readout.mono fun _ holds => ⟨holds.1, holds.2.1⟩)
  have atFiber := conditional.congr_ae outer.measurable
    (readout.mono fun _ holds => holds.2.2)
  rwa [atFiber.unique outer] at joint

/-- The iterated size bound is the size bound under the bind. -/
theorem sizeFinite_bind_iff (measure : Measure source) (kernel : Kernel source target)
    {integrand : β → selection.Carrier}
    (measurable : MeasurableMap target borel integrand) :
    ENNReal.Finite (lintegral (measure.bind kernel)
        (fun y => ENNReal.ofReal (abs (integrand y)))) ↔
      ENNReal.Finite (lintegral measure (fun x =>
        lintegral (kernel x) (fun y => ENNReal.ofReal (abs (integrand y))))) := by
  rw [Measure.lintegral_bind measure kernel (abs_measurable measurable)]

/-- Finite size under a bind certifies almost every fiber. The fibers' sizes
integrate to the bind's size, so they are finite almost everywhere, and a
measurable integrand of finite size has a certified integral. -/
theorem ae_hasRealIntegral_of_sizeFinite_bind (measure : Measure source)
    (kernel : Kernel source target) {integrand : β → selection.Carrier}
    (measurable : MeasurableMap target borel integrand)
    (sizeFinite : ENNReal.Finite (lintegral (measure.bind kernel)
      (fun y => ENNReal.ofReal (abs (integrand y))))) :
    measure.AE fun x => ∃ value, HasRealIntegral (kernel x) integrand value :=
  (ae_finite_of_lintegral_finite measure
      (Kernel.lintegral_measurable kernel (abs_measurable measurable))
      ((sizeFinite_bind_iff measure kernel measurable).mp sizeFinite)).mono
    fun _ fiberFinite => ⟨_, IntegralParts.ofSizeFinite measurable fiberFinite, rfl⟩

/-! ### Witnesses for the bind premises

`NullFiber` has a fiber with no integral at a null input, which the
almost-everywhere premise admits and an everywhere premise refuses.
`Cancelling` has fibers and an outer law that integrate, while the bind does
not, so the iterated size bound is not implied by the other premises. -/

namespace NullFiber

/-! A fiber with no integral at a null input. The law is the point mass at
`false`. From `true` the kernel puts infinite mass on a readout of one. -/

/-- Booleans with every set measurable. -/
abbrev bools : Space Bool := Space.discrete Bool

/-- One at `true` and zero at `false`. -/
noncomputable def reading : Bool → selection.Carrier
  | true => one
  | false => zero

/-- Infinite mass at `true` from `true`, and the point mass at `false` from
`false`. -/
noncomputable def kernel : Kernel bools bools where
  toFun
    | true => Measure.smul ENNReal.top (Measure.dirac bools true)
    | false => Measure.dirac bools false
  measurable := fun _ _ => Space.discrete_measurable _

/-- Every readout of a discrete space is measurable. -/
theorem reading_measurable : MeasurableMap bools borel reading :=
  fun _ => Space.discrete_measurable _

/-- The fiber at `true` has infinite size, so it has no certified integral. An
everywhere fiber premise is false here. -/
theorem fiber_uncertified : ¬∃ value, HasRealIntegral (kernel true) reading value := by
  rintro ⟨value, parts, -⟩
  have size := parts.lintegral_abs_finite
  change ENNReal.Finite (lintegral (Measure.smul ENNReal.top (Measure.dirac bools true))
    (fun y => ENNReal.ofReal (abs (reading y)))) at size
  rw [lintegral_smul_measure, lintegral_dirac bools true (fun _ => Space.discrete_measurable _)]
    at size
  have unit : ENNReal.ofReal (abs (reading true)) = ENNReal.one := by
    show ENNReal.ofReal (abs one) = ENNReal.one
    rw [abs_of_nonnegative (le_of_lt one_positive), ENNReal.ofReal_one]
  rw [unit, ENNReal.top_mul_of_ne_zero ENNReal.one_ne_zero] at size
  exact size

/-- The bind still integrates the readout, to the explicit mean zero: the bad
fiber is null under the point mass at `false`. -/
theorem bind_mean :
    HasRealIntegral ((Measure.dirac bools false).bind kernel) reading zero := by
  have atFalse : HasRealIntegral (kernel false) reading zero :=
    hasRealIntegral_dirac bools false reading_measurable
  have fibers : (Measure.dirac bools false).AE fun x =>
      HasRealIntegral (kernel x) reading zero := by
    show Measure.dirac bools false
      (Set.complement fun x => HasRealIntegral (kernel x) reading zero) = ENNReal.zero
    exact Measure.dirac_apply_of_not_mem bools false (Space.discrete_measurable _)
      fun failure => failure atFalse
  refine hasRealIntegral_bind _ kernel (fiber := fun _ => zero) reading_measurable ?_ fibers
    (hasRealIntegral_dirac bools false (fun _ => Space.discrete_measurable _))
  rw [lintegral_dirac bools false (fun _ => Space.discrete_measurable _)]
  change ENNReal.Finite (lintegral (Measure.dirac bools false)
    (fun y => ENNReal.ofReal (abs (reading y))))
  rw [lintegral_dirac bools false (fun _ => Space.discrete_measurable _)]
  exact ENNReal.ofReal_finite _

end NullFiber

namespace Cancelling

/-! Fibers that cancel under an infinite outer mass. Every fiber is the pair of
point masses at `true` and `false` with readout `+1` and `-1`, so it integrates
to zero, and so does the outer law. The bind carries infinite mass on a readout
of size one, so it has no certified integral. -/

/-- Booleans with every set measurable. -/
abbrev bools : Space Bool := Space.discrete Bool

/-- The one-point space. -/
abbrev point : Space Unit := Space.discrete Unit

/-- The readout's positive part, one at `true`. -/
noncomputable def positivePart : Bool → NNReal
  | true => NNReal.one
  | false => NNReal.zero

/-- The readout's negative part, one at `false`. -/
noncomputable def negativePart : Bool → NNReal
  | true => NNReal.zero
  | false => NNReal.one

/-- `+1` at `true` and `-1` at `false`. -/
noncomputable def reading (outcome : Bool) : selection.Carrier :=
  sub (positivePart outcome).toReal (negativePart outcome).toReal

/-- The point masses at `true` and `false`. -/
noncomputable def pair : Measure bools :=
  Measure.add (Measure.dirac bools true) (Measure.dirac bools false)

/-- Every input draws the pair. -/
noncomputable def kernel : Kernel point bools where
  toFun _ := pair
  measurable := fun _ _ => Space.discrete_measurable _

/-- Infinite mass on the one input. -/
noncomputable def outer : Measure point :=
  Measure.smul ENNReal.top (Measure.dirac point ())

/-- Each fiber integrates the readout to zero. -/
theorem fiber_mean (input : Unit) : HasRealIntegral (kernel input) reading zero := by
  refine ⟨{ positive := positivePart
            negative := negativePart
            positive_measurable := fun _ => Space.discrete_measurable _
            negative_measurable := fun _ => Space.discrete_measurable _
            decomposition := fun _ => rfl
            positiveMass := NNReal.one
            negativeMass := NNReal.one
            positive_integral := ?_
            negative_integral := ?_ }, sub_self _⟩
  · change lintegral pair (fun y => ENNReal.finite (positivePart y)) = _
    rw [pair, lintegral_add_measure, lintegral_dirac bools true (fun _ => Space.discrete_measurable _),
      lintegral_dirac bools false (fun _ => Space.discrete_measurable _)]
    exact ENNReal.add_zero _
  · change lintegral pair (fun y => ENNReal.finite (negativePart y)) = _
    rw [pair, lintegral_add_measure, lintegral_dirac bools true (fun _ => Space.discrete_measurable _),
      lintegral_dirac bools false (fun _ => Space.discrete_measurable _)]
    exact ENNReal.zero_add _

/-- The outer law integrates the fiber means, all zero, to zero. -/
theorem outer_mean : HasRealIntegral outer (fun _ => zero) zero := by
  refine HasRealIntegral.of_lintegral_ofReal (fun _ => Space.discrete_measurable _)
    (fun _ => le_refl zero) (le_refl zero) ?_
  show lintegral outer (fun _ => ENNReal.ofReal zero) = ENNReal.ofReal zero
  rw [ENNReal.ofReal_zero]
  exact lintegral_zero outer

/-- The bind has no certified integral of the readout: its size integrates to
infinity. -/
theorem bind_uncertified : ¬∃ value, HasRealIntegral (outer.bind kernel) reading value := by
  rintro ⟨value, parts, -⟩
  have size := parts.lintegral_abs_finite
  rw [Measure.lintegral_bind outer kernel (fun _ => Space.discrete_measurable _)] at size
  change ENNReal.Finite (lintegral (Measure.smul ENNReal.top (Measure.dirac point ()))
    (fun _ => lintegral pair (fun y => ENNReal.ofReal (abs (reading y))))) at size
  rw [lintegral_smul_measure, lintegral_dirac point () (fun _ => Space.discrete_measurable _),
    pair, lintegral_add_measure,
    lintegral_dirac bools true (fun _ => Space.discrete_measurable _),
    lintegral_dirac bools false (fun _ => Space.discrete_measurable _)] at size
  have unit : ENNReal.ofReal (abs (reading true)) = ENNReal.one := by
    show ENNReal.ofReal (abs (sub NNReal.one.toReal NNReal.zero.toReal)) = ENNReal.one
    rw [NNReal.toReal_one, NNReal.toReal_zero, sub_zero,
      abs_of_nonnegative (le_of_lt one_positive), ENNReal.ofReal_one]
  have nonzero : ENNReal.add (ENNReal.ofReal (abs (reading true)))
      (ENNReal.ofReal (abs (reading false))) ≠ ENNReal.zero := fun vanishes => by
    rw [unit] at vanishes
    exact ENNReal.one_ne_zero (ENNReal.add_eq_zero_iff.mp vanishes).1
  rw [ENNReal.top_mul_of_ne_zero nonzero] at size
  exact size

end Cancelling

end Problib.Inference.Derivative.Continuous
