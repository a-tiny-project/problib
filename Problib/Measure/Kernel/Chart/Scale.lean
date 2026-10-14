module

public import Problib.Measure.Kernel.Chart.Split
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Real.Scale
public import Problib.Measure.Integral.Density.AlmostEverywhere

/-! # Scaling a draw by its parameter

A draw `x` scaled by `θ` spreads over the line when `θ ≠ 0` and collapses to
the origin when `θ = 0`. No one chart family follows both, so the reference
is a split: a line chart on the nonzero parameters and a point chart at zero.
Against line volume the law has the source's density read back through the
inverse scale and weighted by `|θ|⁻¹`. At zero the law is the source's total
mass at the origin, and its density against the point is that mass: one
exactly when the source is a probability.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Real.Construction
open Problib.Real.Construction.Dedekind (mul mul_assoc one_mul zero_mul mul_inverse_cancel inverse_nonzero)
open Problib.Measure.Real (borel Carrier volume volumePi volumePi_zero volumePi_one lineVector
  lineVector_measurable measurable_eq scaleJacobian scale_measurable_any map_withDensity_volume_scale)

public section

/-- The identity chart of the line, live at nonzero parameters. -/
@[expose] public noncomputable def scaleLineChart : Chart borel 1 1 where
  domain := fun θ _ => θ ≠ Dedekind.zero
  map := fun _ input => input
  jacobian := fun _ _ => Dedekind.one
  member := fun θ _ => θ ≠ Dedekind.zero
  inverse := fun _ point => point
  domain_measurable := (Space.product borel _).complement
    (measurable_eq (Space.first_measurable _ _) (MeasurableMap.constant _ _ Dedekind.zero))
  map_measurable := Space.second_measurable _ _
  jacobian_measurable := MeasurableMap.constant _ _ _
  member_measurable := (Space.product borel _).complement
    (measurable_eq (Space.first_measurable _ _) (MeasurableMap.constant _ _ Dedekind.zero))
  inverse_measurable := Space.second_measurable _ _
  injective := fun _ _ _ _ _ equal => equal
  member_iff := fun _ point =>
    ⟨fun nonzero => ⟨point, nonzero, rfl⟩, fun ⟨_, nonzero, _⟩ => nonzero⟩
  inverse_domain := fun _ _ nonzero => nonzero
  map_inverse := fun _ _ _ => rfl

/-- The chart of the origin, live at the zero parameter. -/
@[expose] public noncomputable def scalePointChart : Chart borel 0 1 where
  domain := fun θ _ => θ = Dedekind.zero
  map := fun _ _ _ => Dedekind.zero
  jacobian := fun _ _ => Dedekind.one
  member := fun θ point => θ = Dedekind.zero ∧ point 0 = Dedekind.zero
  inverse := fun _ _ index => Fin.elim0 index
  domain_measurable := measurable_eq (Space.first_measurable _ _) (MeasurableMap.constant _ _ Dedekind.zero)
  map_measurable := MeasurableMap.constant _ _ _
  jacobian_measurable := MeasurableMap.constant _ _ _
  member_measurable := (Space.product borel _).inter (measurable_eq (Space.first_measurable _ _) (MeasurableMap.constant _ _ Dedekind.zero))
    (measurable_eq (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin 1 => borel) 0)
      (Space.second_measurable _ _)) (MeasurableMap.constant _ _ Dedekind.zero))
  inverse_measurable := MeasurableMap.constant _ _ _
  injective := fun _ _ _ _ _ _ => funext fun index => Fin.elim0 index
  member_iff := fun _ point => by
    constructor
    · rintro ⟨atZero, origin⟩
      refine ⟨fun index => Fin.elim0 index, atZero, funext fun coordinate => ?_⟩
      have first : coordinate = 0 := Fin.ext (by omega)
      subst first
      exact origin.symm
    · rintro ⟨_, atZero, rfl⟩
      exact ⟨atZero, rfl⟩
  inverse_domain := fun _ _ member => member.1
  map_inverse := fun _ point member => by
    funext coordinate
    have first : coordinate = 0 := Fin.ext (by omega)
    subst first
    exact member.2.symm

/-- Piece zero holds the nonzero parameters, piece one holds zero. -/
@[expose] public noncomputable def scalePiece (θ : Carrier) : Nat := by
  classical
  exact if θ = Dedekind.zero then 1 else 0

/-- The line chart away from zero and the point chart at zero. -/
@[expose] public noncomputable def scaleSplit : Split borel 1 where
  piece := scalePiece
  piece_measurable := fun index => by
    classical
    rcases index with _ | _ | later
    · have equal : (fun θ => scalePiece θ = 0) = (fun θ => θ ≠ Dedekind.zero) := by
        funext θ
        unfold scalePiece
        by_cases atZero : θ = Dedekind.zero <;> simp [atZero]
      rw [equal]
      exact borel.complement (measurable_eq (MeasurableMap.identity borel) (MeasurableMap.constant _ _ Dedekind.zero))
    · have equal : (fun θ => scalePiece θ = 0 + 1) = (fun θ => θ = Dedekind.zero) := by
        funext θ
        unfold scalePiece
        by_cases atZero : θ = Dedekind.zero <;> simp [atZero]
      rw [equal]
      exact measurable_eq (MeasurableMap.identity borel) (MeasurableMap.constant _ _ Dedekind.zero)
    · have equal : (fun θ => scalePiece θ = later + 1 + 1) = Set.empty := by
        funext θ
        unfold scalePiece
        by_cases atZero : θ = Dedekind.zero <;> simp [atZero, Set.empty]
      rw [equal]
      exact borel.empty
  family := fun index => match index with
    | 0 => Family.single scaleLineChart
    | _ + 1 => Family.single scalePointChart

public theorem scaled_measurable :
    MeasurableMap (Space.product borel borel) (Space.pi fun _ : Fin 1 => borel)
      (fun pair => lineVector (mul pair.1 pair.2)) :=
  MeasurableMap.comp lineVector_measurable
    (Problib.Measure.Real.measurable_mul (left := fun pair : Carrier × Carrier => pair.1)
      (right := fun pair => pair.2) (Space.first_measurable borel borel)
      (Space.second_measurable borel borel))

/-- The draw from `source` scaled by the parameter, as a one-entry vector. -/
@[expose] public noncomputable def scaleLaw (source : Measure borel) (sourceFinite : Measure.SFinite source) :
    Kernel borel (Space.pi fun _ : Fin 1 => borel) :=
  (Kernel.attach (Kernel.const borel source) (IsSFinite.const borel sourceFinite)).map
    (fun pair => lineVector (mul pair.1 pair.2)) scaled_measurable

public noncomputable def scaleLawSFinite (source : Measure borel) (sourceFinite : Measure.SFinite source) :
    IsSFinite (scaleLaw source sourceFinite) :=
  IsSFinite.map (IsSFinite.attach _) _ _

public theorem scaleLaw_apply (source : Measure borel) (sourceFinite : Measure.SFinite source)
    (θ : Carrier) :
    scaleLaw source sourceFinite θ =
      (source.map (mul θ) (scale_measurable_any θ)).map lineVector lineVector_measurable := by
  change (source.map (fun value => (θ, value)) _).map _ _ = _
  rw [Measure.map_comp, Measure.map_comp]

private theorem unit_density {dimension : Nat} (domain : Set (Fin dimension → Carrier))
    (inside : ∀ input, domain input) :
    ennrealIndicator domain (fun _ => ENNReal.ofReal Dedekind.one) = fun _ => ENNReal.one := by
  funext input
  rw [ennrealIndicator_of_mem (inside input)]
  exact ENNReal.ofReal_one

/-- Away from zero, the split's reference is line volume. -/
public theorem scaleSplit_reference_of_nonzero {θ : Carrier} (nonzero : θ ≠ Dedekind.zero) :
    scaleSplit.reference θ = volumePi 1 := by
  have piece : scalePiece θ = 0 := by
    unfold scalePiece
    simp [nonzero]
  rw [Split.reference_apply]
  change (scaleSplit.family (scalePiece θ)).reference θ = _
  rw [piece]
  change (Family.single scaleLineChart).reference θ = _
  rw [Family.single_reference]
  have unit : ennrealIndicator (scaleLineChart.domain θ)
      (fun input => ENNReal.ofReal (scaleLineChart.jacobian θ input)) = fun _ => ENNReal.one :=
    unit_density _ fun _ => nonzero
  rw [unit]
  rw [Measure.withDensity_one]
  exact Measure.map_id _

/-- At zero, the split's reference is the unit mass at the origin. -/
public theorem scaleSplit_reference_zero :
    scaleSplit.reference Dedekind.zero = Measure.dirac _ (fun _ => Dedekind.zero) := by
  have piece : scalePiece Dedekind.zero = 1 := by
    unfold scalePiece
    simp
  rw [Split.reference_apply]
  change (scaleSplit.family (scalePiece Dedekind.zero)).reference Dedekind.zero = _
  rw [piece]
  change (Family.single scalePointChart).reference Dedekind.zero = _
  rw [Family.single_reference]
  have unit : ennrealIndicator (scalePointChart.domain Dedekind.zero)
      (fun input => ENNReal.ofReal (scalePointChart.jacobian Dedekind.zero input)) =
        fun _ => ENNReal.one :=
    unit_density _ fun _ => rfl
  rw [unit]
  rw [Measure.withDensity_one, volumePi_zero]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable, Measure.dirac_apply _ _ setMeasurable,
    Measure.dirac_apply _ _ (show (Space.pi fun _ : Fin 0 => borel).Measurable
      (Set.preimage (scalePointChart.map Dedekind.zero) set) from
        section_measurable scalePointChart.map_measurable Dedekind.zero setMeasurable)]
  rfl

/-- Away from zero the scaled law has, against line volume, the source's
density read at `θ⁻¹·y` and weighted by `|θ⁻¹|`. -/
public theorem scale_isDensity_of_nonzero (source : Measure borel) (sourceFinite : Measure.SFinite source)
    {density : Carrier → ENNReal} (densityMeasurable : ENNRealMeasurable borel density)
    (sourceDensity : source = volume.withDensity density) {θ : Carrier} (nonzero : θ ≠ Dedekind.zero) :
    Measure.IsDensity (scaleLaw source sourceFinite θ) (scaleSplit.reference θ)
      (fun point => ENNReal.mul (scaleJacobian (Dedekind.inverse θ)) (density (mul (Dedekind.inverse θ) (point 0)))) := by
  have weighted : ENNRealMeasurable borel
      (fun value => ENNReal.mul (scaleJacobian (Dedekind.inverse θ)) (density (mul (Dedekind.inverse θ) value))) :=
    ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _)
      (densityMeasurable.comp (scale_measurable_any (Dedekind.inverse θ)))
  have scaled : source.map (mul θ) (scale_measurable_any θ) =
      volume.withDensity
        (fun value => ENNReal.mul (scaleJacobian (Dedekind.inverse θ)) (density (mul (Dedekind.inverse θ) value))) := by
    rw [sourceDensity]
    conv => lhs; rw [← map_withDensity_volume_scale (Dedekind.inverse θ) (inverse_nonzero nonzero)]
    rw [← Measure.map_withDensity _ (mul (Dedekind.inverse θ)) (scale_measurable_any (Dedekind.inverse θ))
        densityMeasurable,
      Measure.withDensity_withDensity _ (ENNRealMeasurable.constant _ _)
        (densityMeasurable.comp (scale_measurable_any (Dedekind.inverse θ))),
      Measure.map_comp]
    have cancel : (fun value => mul θ (mul (Dedekind.inverse θ) value)) = fun value => value := by
      funext value
      rw [← mul_assoc, mul_inverse_cancel nonzero, one_mul]
    simp only [cancel]
    exact Measure.map_id _
  unfold Measure.IsDensity
  rw [scaleLaw_apply, scaleSplit_reference_of_nonzero nonzero, scaled, volumePi_one,
    ← Measure.map_withDensity volume lineVector lineVector_measurable
      (weighted.comp (Space.coordinate_measurable (fun _ : Fin 1 => borel) 0))]
  rfl

/-- At zero the scaled law has, against the unit mass at the origin, the
constant density equal to the source's total mass. -/
public theorem scale_isDensity_zero (source : Measure borel) (sourceFinite : Measure.SFinite source) :
    Measure.IsDensity (scaleLaw source sourceFinite Dedekind.zero) (scaleSplit.reference Dedekind.zero)
      (fun _ => source Set.univ) := by
  unfold Measure.IsDensity
  rw [scaleLaw_apply, scaleSplit_reference_zero, Measure.withDensity_const, Measure.map_comp]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable, Measure.smul_apply_measurable _ _ setMeasurable,
    Measure.dirac_apply _ _ setMeasurable]
  classical
  have collapse : (fun value => lineVector (mul Dedekind.zero value)) = fun _ => fun _ => Dedekind.zero := by
    funext value
    rw [zero_mul]
    rfl
  simp only [collapse]
  by_cases origin : set (fun _ => Dedekind.zero)
  · simp only [origin, ↓reduceIte, ENNReal.mul_one]
    have whole : Set.preimage (fun _ : Carrier => (fun _ : Fin 1 => Dedekind.zero)) set = Set.univ := by
      funext value
      exact propext ⟨fun _ => True.intro, fun _ => origin⟩
    rw [whole]
  · simp only [origin, ↓reduceIte, ENNReal.mul_zero]
    have empty : Set.preimage (fun _ : Carrier => (fun _ : Fin 1 => Dedekind.zero)) set = Set.empty := by
      funext value
      exact propext ⟨fun member => origin member, False.elim⟩
    rw [empty]
    exact Measure.empty_apply source

/-- A probability source scaled by zero is exactly the reference's unit mass. -/
public theorem scaleLaw_zero_of_probability (source : Measure borel) (sourceFinite : Measure.SFinite source)
    (probability : source Set.univ = ENNReal.one) :
    scaleLaw source sourceFinite Dedekind.zero = scaleSplit.reference Dedekind.zero := by
  rw [scale_isDensity_zero source sourceFinite, probability, Measure.withDensity_one]

/-- A scaled law whose source has a density has a jointly measurable density
against the split's reference. -/
public noncomputable def scaleDerivative (source : Measure borel) (sourceFinite : Measure.SFinite source)
    {density : Carrier → ENNReal} (densityMeasurable : ENNRealMeasurable borel density)
    (sourceDensity : source = volume.withDensity density) :
    RadonNikodymDerivative (scaleLaw source sourceFinite) scaleSplit.reference :=
  scaleSplit.derivative _ (scaleLawSFinite source sourceFinite) fun θ => by
    rw [← Split.reference_apply]
    by_cases atZero : θ = Dedekind.zero
    · subst atZero
      rw [scale_isDensity_zero source sourceFinite]
      exact Measure.absolutelyContinuous_withDensity _ _
    · rw [scale_isDensity_of_nonzero source sourceFinite densityMeasurable sourceDensity atZero]
      exact Measure.absolutelyContinuous_withDensity _ _

end

end Problib.Measure.Kernel.Chart
