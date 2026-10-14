module

public import Problib.Measure.Kernel.Chart.Stratum
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Analysis.Real.FiniteVector

/-! # The reference of a chart family

Each chart contributes Jacobian-weighted volume on the inputs whose image point
selects it, pushed forward through the chart. Summing those contributions over
the charts gives the family's reference, a kernel in the parameter.

The reference must be a countable sum of finite kernels. Each chart's selected
inputs are cut by increasing bounds: the box `[-k, k]ᵈ` and a Jacobian below
`k`. Consecutive bounds are differenced into disjoint shells, so the shells
partition the selected inputs and their contributions sum to the chart's
contribution exactly. Each shell's contribution has mass at most `k` times the
box's volume, at every parameter.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Real.Construction.Dedekind
open Problib.Measure.Real (borel Carrier volumePi volumePiSFinite centeredBox centeredBox_measurable
  volumePi_centeredBox_finite measurable_iio ofReal_measurable)
open Problib.Analysis.Real.FiniteVector (supNorm coordinate_le_supNorm maxReal le_max_left
  le_max_right)
open Problib.Analysis.Real (abs_le)

public section

universe u

variable {Θ : Type u} {parameter : Space Θ} {ambient : Nat}
  (family : Family parameter ambient)

/-- Inputs of chart `index` whose image point selects that chart, as pairs of a
parameter and an input. -/
@[expose] public def Family.selectedInputs (index : Nat) :
    Set (Θ × (Fin (family.dimension index) → Carrier)) :=
  fun pair => (family.chart index).domain pair.1 pair.2 ∧
    family.Selected index pair.1 ((family.chart index).map pair.1 pair.2)

public theorem Family.selectedInputs_measurable (index : Nat) :
    (Space.product parameter (Space.pi fun _ : Fin (family.dimension index) => borel)).Measurable
      (family.selectedInputs index) :=
  (Space.product parameter _).inter (family.chart index).domain_measurable
    (Space.pair_measurable (Space.first_measurable _ _) (family.chart index).map_measurable
      (family.selected_measurable index))

/-- The bound `bound`: selected inputs in `[-bound, bound]ᵈ` whose Jacobian is
below `bound`. -/
@[expose] public def Family.bounded (index bound : Nat) :
    Set (Θ × (Fin (family.dimension index) → Carrier)) :=
  fun pair => family.selectedInputs index pair ∧ centeredBox _ bound pair.2 ∧
    lt ((family.chart index).jacobian pair.1 pair.2) (selection.ofRat (bound : Rat))

public theorem Family.bounded_measurable (index bound : Nat) :
    (Space.product parameter (Space.pi fun _ : Fin (family.dimension index) => borel)).Measurable
      (family.bounded index bound) :=
  (Space.product parameter _).inter (family.selectedInputs_measurable index)
    ((Space.product parameter _).inter
      (Space.second_measurable _ _ (centeredBox_measurable _ bound))
      ((family.chart index).jacobian_measurable (measurable_iio _)))

/-- Every selected input lies within some bound. -/
public theorem Family.exists_bounded {index : Nat}
    {pair : Θ × (Fin (family.dimension index) → Carrier)}
    (selected : family.selectedInputs index pair) : ∃ bound, family.bounded index bound pair := by
  rcases exists_nat_strict_upper
      (maxReal (supNorm pair.2) ((family.chart index).jacobian pair.1 pair.2)) with ⟨bound, above⟩
  refine ⟨bound, selected, fun coordinate => ?_, Problib.Real.Construction.Dedekind.lt_of_le_of_lt (le_max_right _ _) above⟩
  exact abs_le.mp (Problib.Real.Construction.Dedekind.le_trans (coordinate_le_supNorm pair.2 coordinate)
    (Problib.Real.Construction.Dedekind.le_of_lt (Problib.Real.Construction.Dedekind.lt_of_le_of_lt (le_max_left _ _) above)))

/-- The shells: each bound less the bounds before it. -/
@[expose] public def Family.shell (index : Nat) :
    Nat → Set (Θ × (Fin (family.dimension index) → Carrier)) :=
  Set.disjointed (family.bounded index)

public theorem Family.shell_measurable (index bound : Nat) :
    (Space.product parameter (Space.pi fun _ : Fin (family.dimension index) => borel)).Measurable
      (family.shell index bound) :=
  (Space.product parameter _).disjointed_measurable (family.bounded_measurable index) bound

public theorem Family.shell_bounded {index bound : Nat}
    {pair : Θ × (Fin (family.dimension index) → Carrier)}
    (inside : family.shell index bound pair) : family.bounded index bound pair :=
  Set.disjointed_subset _ bound inside

/-- The shells partition the selected inputs. -/
public theorem Family.iUnion_shell (index : Nat) :
    Set.iUnion (family.shell index) = family.selectedInputs index := by
  rw [Family.shell, Set.iUnion_disjointed]
  apply Set.ext
  intro pair
  constructor
  · rintro ⟨bound, inside⟩
    exact inside.1
  · intro selected
    exact family.exists_bounded selected

/-- The density on one shell: the Jacobian there, zero elsewhere. -/
@[expose] public noncomputable def Family.shellDensity (index bound : Nat) (θ : Θ)
    (input : Fin (family.dimension index) → Carrier) : ENNReal :=
  ennrealIndicator (family.shell index bound)
    (fun pair => ENNReal.ofReal ((family.chart index).jacobian pair.1 pair.2)) (θ, input)

public theorem Family.shellDensity_measurable (index bound : Nat) :
    ENNRealMeasurable
      (Space.product parameter (Space.pi fun _ : Fin (family.dimension index) => borel))
      (fun pair => family.shellDensity index bound pair.1 pair.2) :=
  ENNRealMeasurable.indicator (family.shell_measurable index bound)
    (ofReal_measurable.comp (family.chart index).jacobian_measurable)

private theorem shellDensity_le (index bound : Nat) (θ : Θ)
    (input : Fin (family.dimension index) → Carrier) :
    ENNReal.le (family.shellDensity index bound θ input)
      (ENNReal.ofReal (selection.ofRat (bound : Rat))) := by
  classical
  unfold Family.shellDensity ennrealIndicator ennrealPiecewise
  by_cases inside : family.shell index bound (θ, input)
  · simp only [inside, ↓reduceIte]
    exact ENNReal.ofReal_monotone (Problib.Real.Construction.Dedekind.le_of_lt (family.shell_bounded inside).2.2)
  · simp only [inside, ↓reduceIte]
    exact ENNReal.zero_le _

private theorem shellDensity_outside_box {index bound : Nat} {θ : Θ}
    {input : Fin (family.dimension index) → Carrier} (outside : ¬centeredBox _ bound input) :
    family.shellDensity index bound θ input = ENNReal.zero := by
  classical
  unfold Family.shellDensity ennrealIndicator ennrealPiecewise
  have absent : ¬family.shell index bound (θ, input) :=
    fun inside => outside (family.shell_bounded inside).2.1
  simp only [absent, ↓reduceIte]

/-- Volume on one box. -/
public noncomputable def boxVolume (dimension bound : Nat) :
    Measure (Space.pi fun _ : Fin dimension => borel) :=
  (volumePi dimension).restrict (centeredBox dimension bound)

public theorem boxVolume_finite (dimension bound : Nat) :
    Measure.IsFinite (boxVolume dimension bound) :=
  ⟨by rw [boxVolume, Measure.restrict_apply_univ]; exact volumePi_centeredBox_finite _ _⟩

/-- One shell's weighted volume, as a finite kernel. -/
public noncomputable def Family.shellKernel (index bound : Nat) :
    Kernel parameter (Space.pi fun _ : Fin (family.dimension index) => borel) :=
  (Kernel.const parameter (boxVolume _ bound)).withDensity
    (IsFinite.const parameter (boxVolume_finite _ bound)).toSFinite
    (family.shellDensity index bound) (family.shellDensity_measurable index bound)

public theorem Family.shellKernel_finite (index bound : Nat) : IsFinite (family.shellKernel index bound) :=
  IsFinite.withDensity_of_bounded (IsFinite.const parameter (boxVolume_finite _ bound))
    (family.shellDensity_measurable index bound) (ENNReal.ofReal_finite _)
    (shellDensity_le family index bound)

/-- One shell's contribution: Jacobian-weighted volume on the shell, pushed
through the chart. -/
@[expose] public noncomputable def Family.component (index bound : Nat) :
    Kernel parameter (Space.pi fun _ : Fin ambient => borel) :=
  ((family.shellKernel index bound).attach (family.shellKernel_finite index bound).toSFinite).map
    (fun pair => (family.chart index).map pair.1 pair.2) (family.chart index).map_measurable

/-- Each shell's contribution is a finite kernel: its mass is at most `bound`
times the volume of the box, at every parameter. -/
public theorem Family.component_finite (index bound : Nat) : IsFinite (family.component index bound) :=
  ((family.shellKernel_finite index bound).attach).map _ (family.chart index).map_measurable

/-- A shell's contribution at one parameter. -/
public theorem Family.component_apply (index bound : Nat) (θ : Θ) :
    family.component index bound θ =
      ((volumePi _).withDensity (family.shellDensity index bound θ)).map
        ((family.chart index).map θ) (section_measurable (family.chart index).map_measurable θ) := by
  have unboxed : (boxVolume (family.dimension index) bound).withDensity
      (family.shellDensity index bound θ) =
        (volumePi _).withDensity (family.shellDensity index bound θ) := by
    rw [boxVolume, ← Measure.withDensity_indicator _ _ (centeredBox_measurable _ bound)]
    congr 1
    funext input
    classical
    unfold ennrealIndicator ennrealPiecewise
    by_cases inside : centeredBox _ bound input
    · simp only [inside, ↓reduceIte]
    · simp only [inside, ↓reduceIte, shellDensity_outside_box family inside]
  have unfolded : family.component index bound θ =
      ((family.shellKernel index bound θ).map (fun value => (θ, value))
        (pair_left_measurable θ)).map (fun pair => (family.chart index).map pair.1 pair.2)
        (family.chart index).map_measurable := rfl
  rw [unfolded, Measure.map_comp]
  exact congrArg (fun measure => measure.map ((family.chart index).map θ)
    (section_measurable (family.chart index).map_measurable θ)) unboxed

/-- The reference of a chart family: the sum of every chart's shells. -/
@[expose] public noncomputable def Family.reference :
    Kernel parameter (Space.pi fun _ : Fin ambient => borel) :=
  Kernel.sum (Kernel.flatten family.component)

/-- The reference is globally s-finite, by its shells. -/
public noncomputable def Family.referenceSFinite : IsSFinite family.reference where
  components := Kernel.flatten family.component
  finite := fun _ => family.component_finite _ _
  sum_eq := rfl

/-- The reference sums every chart's shells. -/
public theorem Family.reference_eq_sum :
    family.reference = Kernel.sum (fun index => Kernel.sum (family.component index)) :=
  Kernel.sum_double _

/-- The density of a chart's whole contribution: the Jacobian on its selected
inputs, zero elsewhere. -/
@[expose] public noncomputable def Family.selectedDensity (index : Nat) (θ : Θ)
    (input : Fin (family.dimension index) → Carrier) : ENNReal :=
  ennrealIndicator (family.selectedInputs index)
    (fun pair => ENNReal.ofReal ((family.chart index).jacobian pair.1 pair.2)) (θ, input)

/-- A chart's shells sum to Jacobian-weighted volume on its selected inputs,
pushed through the chart. -/
public theorem Family.sum_component (index : Nat) (θ : Θ) :
    Measure.sum (fun bound => family.component index bound θ) =
      ((volumePi _).withDensity (family.selectedDensity index θ)).map
        ((family.chart index).map θ) (section_measurable (family.chart index).map_measurable θ) := by
  classical
  simp only [family.component_apply]
  rw [← Measure.map_sum, ← Measure.withDensity_tsum _ _
    (fun bound => Kernel.jointly_measurable_slice (family.shellDensity_measurable index bound) θ)]
  congr 2
  funext input
  by_cases selected : family.selectedInputs index (θ, input)
  · have covered : Set.iUnion (family.shell index) (θ, input) := by
      rw [family.iUnion_shell]
      exact selected
    rcases covered with ⟨bound, inside⟩
    rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ bound]
    · unfold Family.shellDensity Family.selectedDensity ennrealIndicator ennrealPiecewise
      simp only [inside, selected, ↓reduceIte]
    · intro other different
      have absent : ¬family.shell index other (θ, input) := fun otherInside =>
        Set.disjointed_pairwise _ other bound different otherInside inside
      unfold Family.shellDensity ennrealIndicator ennrealPiecewise
      simp only [absent, ↓reduceIte]
  · have absent : ∀ bound, ¬family.shell index bound (θ, input) := fun bound inside =>
      selected (family.shell_bounded inside).1
    unfold Family.shellDensity Family.selectedDensity ennrealIndicator ennrealPiecewise
    simp only [absent, selected, ↓reduceIte]
    exact ENNReal.tsum_zero

end

end Problib.Measure.Kernel.Chart
