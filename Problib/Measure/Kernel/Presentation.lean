module

public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Integral.Real
public import Problib.Measure.Additive.Map

set_option autoImplicit false

/-!
A presentation of a kernel is a joint kernel on a trace space and a return map
whose pushforward of the joint is the kernel at every input. Transports of
integrals move between the two by `lintegral_map` and `HasRealIntegral.map`.
-/

namespace Problib.Measure

open Problib.Real Problib.Measure.Real

universe u v w t

namespace Kernel

variable {α : Type u} {τ : Type v} {β : Type w}
  {source : Space α} {trace : Space τ} {result : Space β}

/-- The section of a jointly measurable return at one input is measurable. -/
public theorem section_measurable {ret : α × τ → β}
    (measurable : MeasurableMap (Space.product source trace) result ret) (input : α) :
    MeasurableMap trace result (fun point => ret (input, point)) :=
  MeasurableMap.comp measurable (pair_left_measurable (source := source) (target := trace) input)

/-- The return pushes the joint forward to the kernel at every input. -/
@[expose] public def Presents (kernel : Kernel source result) (joint : Kernel source trace)
    (ret : α × τ → β) (measurable : MeasurableMap (Space.product source trace) result ret) :
    Prop :=
  ∀ input, (joint input).map (fun point => ret (input, point))
    (section_measurable measurable input) = kernel input

/-- A presentation of a kernel: a trace space, an s-finite joint on it, and a
jointly measurable return that pushes the joint forward to the kernel. -/
public structure Presentation (kernel : Kernel source result) : Type (max u w (t + 1)) where
  Trace : Type t
  space : Space Trace
  joint : Kernel source space
  finite : IsSFinite joint
  ret : α × Trace → β
  measurable : MeasurableMap (Space.product source space) result ret
  presents : Presents kernel joint ret measurable

/-- A kernel presents itself with the result as its trace. -/
@[expose] public noncomputable def Presentation.identity (kernel : Kernel source result)
    (finite : IsSFinite kernel) : Presentation.{u, w, w} kernel where
  Trace := β
  space := result
  joint := kernel
  finite := finite
  ret := Prod.snd
  measurable := Space.second_measurable source result
  -- The section of `Prod.snd` is the identity up to beta, and measurability is
  -- a proposition, so `map_id` (Measure/Additive/Map.lean:60) closes it.
  presents := fun input => (kernel input).map_id

/-- The same presentation with the input attached to each trace. Its return
reads the input from the trace, so an input-free integrand of the output is an
input-free integrand of the attached trace. -/
@[expose] public noncomputable def Presentation.attached {kernel : Kernel source result}
    (presentation : Presentation.{u, w, t} kernel) : Presentation.{u, w, max u t} kernel where
  Trace := α × presentation.Trace
  space := Space.product source presentation.space
  joint := Kernel.attach presentation.joint presentation.finite
  finite := presentation.finite.attach
  ret := fun pair => presentation.ret pair.2
  measurable := MeasurableMap.comp presentation.measurable
    (Space.second_measurable source (Space.product source presentation.space))
  presents := fun input => by
    rw [Kernel.attach_apply, Measure.map_comp]
    · exact presentation.presents input
    · exact section_measurable (MeasurableMap.comp presentation.measurable
        (Space.second_measurable source (Space.product source presentation.space))) input

/-- A constant joint with an input-free return presents a constant kernel
exactly when the return pushes the joint law to the target law. -/
public theorem presents_const_iff (inhabited : Nonempty α)
    (target : Measure result) (joint : Measure trace) (ret : τ → β)
    (measurable : MeasurableMap trace result ret) :
    Presents (Kernel.const source target) (Kernel.const source joint) (fun pair => ret pair.2)
        (MeasurableMap.comp measurable (Space.second_measurable source trace)) ↔
      joint.map ret measurable = target := by
  constructor
  · intro presents
    obtain ⟨input⟩ := inhabited
    exact presents input
  · intro pushed _
    exact pushed

/-- A nonnegative integral under the kernel is the integral of the returned
integrand under the joint. -/
public theorem integral_map {kernel : Kernel source result} {joint : Kernel source trace}
    {ret : α × τ → β} {measurable : MeasurableMap (Space.product source trace) result ret}
    (presents : Presents kernel joint ret measurable)
    {integrand : β → ENNReal} (integrandMeasurable : ENNRealMeasurable result integrand)
    (input : α) :
    lintegral (kernel input) integrand =
      lintegral (joint input) (fun point => integrand (ret (input, point))) := by
  rw [← presents input]
  exact lintegral_map (joint input) _ (section_measurable measurable input) integrandMeasurable

/-- A certified signed integral under the kernel is one under the joint, and
conversely. Signed-integral transport (`IntegralParts.comap`,
`HasRealIntegral.map`) keeps both spaces in one universe, so the trace here
shares the result's. -/
public theorem real_integral_map {τ' : Type w} {trace' : Space τ'}
    {kernel : Kernel source result} {joint : Kernel source trace'}
    {ret : α × τ' → β} {measurable : MeasurableMap (Space.product source trace') result ret}
    (presents : Presents kernel joint ret measurable)
    {integrand : β → Carrier} (integrandMeasurable : MeasurableMap result borel integrand)
    (input : α) {value : Carrier} :
    HasRealIntegral (kernel input) integrand value ↔
      HasRealIntegral (joint input) (fun point => integrand (ret (input, point))) value := by
  rw [← presents input]
  constructor
  · rintro ⟨parts, same⟩
    exact ⟨IntegralParts.comap (measure := joint input) (section_measurable measurable input) parts, same⟩
  · exact HasRealIntegral.map (section_measurable measurable input) integrandMeasurable

end Kernel

end Problib.Measure
