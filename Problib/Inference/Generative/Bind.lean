import Problib.Inference.Generative
import Problib.Inference.Trace.Resource

namespace Problib.Inference.Generative

open Problib.Probability

universe u v w x

namespace Model

/-- Sequential composition through one ordered, proof-checked trace append. -/
def bind {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w} {InnerValue : Type x}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    (lossless : Problib.Inference.Trace.Lossless resource)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    (outer : Model (Carrier outerGrade) OuterValue)
    (inner : OuterValue → Model (Carrier innerGrade) InnerValue) :
    Model (Carrier (resource.appendGrade compatible)) InnerValue where
  traceLaw :=
    (FiniteMeasure.joint outer.traceLaw fun outerTrace =>
      (inner (outer.result outerTrace)).traceLaw).map fun traces =>
        resource.append compatible traces.1 traces.2
  result := fun trace =>
    let traces := lossless.split compatible trace
    (inner (outer.result traces.1)).result traces.2

end Model

/-- The dependent reference law transported through checked trace append. -/
def bindReference {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    (outerResult : Carrier outerGrade → OuterValue)
    (outerReference : FiniteMeasure (Carrier outerGrade))
    (innerReference : OuterValue → FiniteMeasure (Carrier innerGrade)) :
    FiniteMeasure (Carrier (resource.appendGrade compatible)) :=
  (FiniteMeasure.joint outerReference fun outerTrace =>
    innerReference (outerResult outerTrace)).map fun traces =>
      resource.append compatible traces.1 traces.2

/-- The chain-rule density recovered from a lossless checked trace split. -/
def bindDensity {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    (lossless : Problib.Inference.Trace.Lossless resource)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    (outerResult : Carrier outerGrade → OuterValue)
    (outerDensity : Carrier outerGrade → NNRat)
    (innerDensity : OuterValue → Carrier innerGrade → NNRat) :
    Carrier (resource.appendGrade compatible) → NNRat :=
  fun trace =>
    let traces := lossless.split compatible trace
    outerDensity traces.1 * innerDensity (outerResult traces.1) traces.2

theorem bind_density_finite
    {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w} {InnerValue : Type x}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    (lossless : Problib.Inference.Trace.Lossless resource)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    [DecidableEq (Carrier outerGrade)] [DecidableEq (Carrier innerGrade)]
    [DecidableEq (Carrier (resource.appendGrade compatible))]
    (outer : Model (Carrier outerGrade) OuterValue)
    (inner : OuterValue → Model (Carrier innerGrade) InnerValue)
    (outerReference : FiniteMeasure (Carrier outerGrade))
    (innerReference : OuterValue → FiniteMeasure (Carrier innerGrade))
    (outerDensity : Carrier outerGrade → NNRat)
    (innerDensity : OuterValue → Carrier innerGrade → NNRat)
    (outerCorrect : FiniteMeasure.IsDensity outer.traceLaw
      outerReference outerDensity)
    (innerCorrect : ∀ value, FiniteMeasure.IsDensity (inner value).traceLaw
      (innerReference value) (innerDensity value)) :
    FiniteMeasure.IsDensity
      (Model.bind resource lossless compatible outer inner).traceLaw
      (bindReference resource compatible outer.result outerReference innerReference)
      (bindDensity resource lossless compatible outer.result outerDensity innerDensity) := by
  have jointCorrect := FiniteMeasure.joint_isDensity outerCorrect fun outerTrace =>
    innerCorrect (outer.result outerTrace)
  unfold bindDensity
  simpa [Model.bind, bindReference] using
    FiniteMeasure.map_isDensity_of_bijection jointCorrect
      (fun traces => resource.append compatible traces.1 traces.2)
      (lossless.split compatible)
      (fun traces => lossless.split_append compatible traces.1 traces.2)
      (lossless.append_split compatible)

theorem bind_density_against_factorized_base
    {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w} {InnerValue : Type x}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    (lossless : Problib.Inference.Trace.Lossless resource)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    [DecidableEq (Carrier outerGrade)] [DecidableEq (Carrier innerGrade)]
    [DecidableEq (Carrier (resource.appendGrade compatible))]
    (outer : Model (Carrier outerGrade) OuterValue)
    (inner : OuterValue → Model (Carrier innerGrade) InnerValue)
    (outerReference : FiniteMeasure (Carrier outerGrade))
    (innerReference : OuterValue → FiniteMeasure (Carrier innerGrade))
    (outerDensity : Carrier outerGrade → NNRat)
    (innerDensity : OuterValue → Carrier innerGrade → NNRat)
    (base : FiniteMeasure (Carrier (resource.appendGrade compatible)))
    (outerCorrect : FiniteMeasure.IsDensity outer.traceLaw
      outerReference outerDensity)
    (innerCorrect : ∀ value, FiniteMeasure.IsDensity (inner value).traceLaw
      (innerReference value) (innerDensity value))
    (factorization : BaseMeasureFactorization base
      (bindReference resource compatible outer.result outerReference innerReference)) :
    FiniteMeasure.IsDensity
      (Model.bind resource lossless compatible outer inner).traceLaw base
      (bindDensity resource lossless compatible outer.result outerDensity innerDensity) :=
  density_against_factorized_base
    (bind_density_finite resource lossless compatible outer inner
      outerReference innerReference outerDensity innerDensity
      outerCorrect innerCorrect)
    factorization

theorem bind_simulate_assess_finite
    {Grade : Type u} {Carrier : Grade → Type v}
    {OuterValue : Type w} {InnerValue : Type x}
    (resource : Problib.Inference.Trace.Resource Grade Carrier)
    (lossless : Problib.Inference.Trace.Lossless resource)
    {outerGrade innerGrade : Grade}
    (compatible : resource.Compatible outerGrade innerGrade)
    [DecidableEq (Carrier outerGrade)] [DecidableEq (Carrier innerGrade)]
    [DecidableEq (Carrier (resource.appendGrade compatible))]
    [DecidableEq InnerValue]
    (outer : Model (Carrier outerGrade) OuterValue)
    (inner : OuterValue → Model (Carrier innerGrade) InnerValue)
    (outerReference : FiniteMeasure (Carrier outerGrade))
    (innerReference : OuterValue → FiniteMeasure (Carrier innerGrade))
    (outerDensity : Carrier outerGrade → NNRat)
    (innerDensity : OuterValue → Carrier innerGrade → NNRat)
    (outerCorrect : FiniteMeasure.IsDensity outer.traceLaw
      outerReference outerDensity)
    (innerCorrect : ∀ value, FiniteMeasure.IsDensity (inner value).traceLaw
      (innerReference value) (innerDensity value)) :
    let model := Model.bind resource lossless compatible outer inner
    let reference :=
      bindReference resource compatible outer.result outerReference innerReference
    let density :=
      bindDensity resource lossless compatible outer.result outerDensity innerDensity
    SimAssessSpecification model reference density
      (simulate model density) (assess model density) := by
  exact simulate_assess_finite _ _ _
    (bind_density_finite resource lossless compatible outer inner
      outerReference innerReference outerDensity innerDensity
      outerCorrect innerCorrect)

end Problib.Inference.Generative
