module

public import Problib.Measure.Kernel.Chart.Fibre
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.AlmostEverywhere

/-! # A line that moves with its parameter

A draw `x` placed at the point `(x, θ)` of the plane lies on the horizontal line
at height `θ`, and the line moves with the parameter. For a nonzero source over
all real parameters, no single s-finite reference dominates every line law; this
file does not prove that. One chart that follows the line gives a reference for
each parameter, and against it the law has the source's density read off the
first coordinate.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real (borel Carrier volume volumePi volumePi_one lineVector lineVector_measurable
  measurable_eq)

public section

/-- The point of the plane at horizontal position `value` on the line at
height `θ`. -/
@[expose] public def linePoint (θ value : Carrier) : Fin 2 → Carrier :=
  fun coordinate => if coordinate.val = 0 then value else θ

public theorem linePoint_measurable :
    MeasurableMap (Space.product borel borel) (Space.pi fun _ : Fin 2 => borel)
      (fun pair => linePoint pair.1 pair.2) := by
  refine Space.pi_measurable fun coordinate => ?_
  by_cases first : coordinate.val = 0
  · simp only [linePoint, first, ↓reduceIte]
    exact Space.second_measurable borel borel
  · simp only [linePoint, first, ↓reduceIte]
    exact Space.first_measurable borel borel

/-- A point at height `θ` is the line point of its first coordinate. -/
public theorem linePoint_first {θ : Carrier} {point : Fin 2 → Carrier} (height : point 1 = θ) :
    linePoint θ (point 0) = point := by
  funext coordinate
  by_cases first : coordinate.val = 0
  · have zero : coordinate = 0 := Fin.ext first
    subst zero
    rfl
  · have one : coordinate = 1 := Fin.ext (by omega)
    subst one
    exact height.symm

/-- The chart of the line at height `θ`, over all of one coordinate, with unit
Jacobian. -/
@[expose] public noncomputable def lineChart : Chart borel 1 2 where
  domain := fun _ => Set.univ
  map := fun θ input => linePoint θ (input 0)
  jacobian := fun _ _ => Dedekind.one
  member := fun θ point => point 1 = θ
  inverse := fun _ point _ => point 0
  domain_measurable := (Space.product borel _).univ
  map_measurable := MeasurableMap.comp linePoint_measurable
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin 1 => borel) 0) (Space.second_measurable _ _)))
  jacobian_measurable := MeasurableMap.constant _ _ _
  member_measurable := measurable_eq
    (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin 2 => borel) 1) (Space.second_measurable _ _))
    (Space.first_measurable _ _)
  inverse_measurable := Space.pi_measurable fun _ =>
    MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin 2 => borel) 0) (Space.second_measurable _ _)
  injective := fun θ first second _ _ equal => by
    funext coordinate
    have zero : coordinate = 0 := Fin.ext (by omega)
    subst zero
    exact congrFun equal 0
  member_iff := fun θ point => by
    constructor
    · intro height
      exact ⟨fun _ => point 0, True.intro, linePoint_first height⟩
    · rintro ⟨input, _, rfl⟩
      rfl
  inverse_domain := fun _ _ _ => True.intro
  map_inverse := fun _ _ height => linePoint_first height

/-- The line chart alone. -/
@[expose] public noncomputable def lineFamily : Family borel 2 :=
  Family.single lineChart

/-- The draw from `source` placed on the line at height `θ`. -/
@[expose] public noncomputable def lineLaw (source : Measure borel) (sourceFinite : Measure.SFinite source) :
    Kernel borel (Space.pi fun _ : Fin 2 => borel) :=
  (Kernel.attach (Kernel.const borel source) (IsSFinite.const borel sourceFinite)).map
    (fun pair => linePoint pair.1 pair.2) linePoint_measurable

public noncomputable def lineLawSFinite (source : Measure borel) (sourceFinite : Measure.SFinite source) :
    IsSFinite (lineLaw source sourceFinite) :=
  IsSFinite.map (IsSFinite.attach _) _ _

public theorem lineLaw_apply (source : Measure borel) (sourceFinite : Measure.SFinite source)
    (θ : Carrier) :
    lineLaw source sourceFinite θ =
      source.map (linePoint θ) (section_measurable linePoint_measurable θ) := by
  change (source.map (fun value => (θ, value)) _).map _ _ = _
  rw [Measure.map_comp]

/-- The line family's reference at `θ` is line volume carried to the line. -/
public theorem lineFamily_reference (θ : Carrier) :
    lineFamily.reference θ = volume.map (linePoint θ) (section_measurable linePoint_measurable θ) := by
  have unit : ennrealIndicator (lineChart.domain θ)
      (fun input => ENNReal.ofReal (lineChart.jacobian θ input)) = fun _ => ENNReal.one := by
    funext input
    rw [ennrealIndicator_of_mem True.intro]
    exact ENNReal.ofReal_one
  unfold lineFamily
  rw [Family.single_reference, unit, Measure.withDensity_one, volumePi_one, Measure.map_comp]
  rfl

/-- A source with a density against line volume puts, at every height, the
same density on the first coordinate against the line's reference. -/
public theorem line_isDensity (source : Measure borel) (sourceFinite : Measure.SFinite source)
    {density : Carrier → ENNReal} (densityMeasurable : ENNRealMeasurable borel density)
    (sourceDensity : source = volume.withDensity density) (θ : Carrier) :
    Measure.IsDensity (lineLaw source sourceFinite θ) (lineFamily.reference θ)
      (fun point => density (point 0)) := by
  unfold Measure.IsDensity
  rw [lineLaw_apply, lineFamily_reference, sourceDensity,
    ← Measure.map_withDensity volume (linePoint θ) (section_measurable linePoint_measurable θ)
      (ENNRealMeasurable.comp densityMeasurable (Space.coordinate_measurable (fun _ : Fin 2 => borel) 0))]
  rfl

/-- A line law whose source has a density has a jointly measurable density
against the line family's reference. -/
public noncomputable def lineDerivative (source : Measure borel) (sourceFinite : Measure.SFinite source)
    {density : Carrier → ENNReal} (densityMeasurable : ENNRealMeasurable borel density)
    (sourceDensity : source = volume.withDensity density) :
    RadonNikodymDerivative (lineLaw source sourceFinite) lineFamily.reference :=
  lineFamily.derivative _ (lineLawSFinite source sourceFinite) fun θ => by
    rw [line_isDensity source sourceFinite densityMeasurable sourceDensity θ]
    exact Measure.absolutelyContinuous_withDensity _ _

end

end Problib.Measure.Kernel.Chart
