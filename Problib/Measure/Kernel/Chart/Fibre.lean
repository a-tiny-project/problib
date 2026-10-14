module

public import Problib.Measure.Kernel.Chart.Shell
public import Problib.Measure.Kernel.RadonNikodym.StandardBorel
public import Problib.Measure.StandardBorel.Pi
public import Problib.Measure.StandardBorel.Real

/-! # Sigma-finite fibers, and the density against a family's reference

At each parameter, the shells' images are disjoint: a point selects one chart,
the chart is injective, and the shells of one chart are disjoint. So on the
image of a shell the reference is that shell's contribution alone, whose mass is
finite, and outside every image the reference is null. The images together with
that null remainder cover the ambient space with pieces of finite reference
mass. Finiteness is measured under the reference itself, never under one
chart's volume.

Sigma-finite fibers turn plain absolute continuity into the zero-infinity
condition that the kernel Radon-Nikodym construction asks for. A law that the
reference covers at every parameter therefore has a jointly measurable density
against it.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Measure.Real (borel Carrier volumePi)

public section

universe u

variable {Θ : Type u} {parameter : Space Θ} {ambient : Nat}
  (family : Family parameter ambient)

/-- The image of one shell at a parameter. -/
@[expose] public def Family.shellImage (index bound : Nat) (θ : Θ) : Set (Fin ambient → Carrier) :=
  (family.chart index).image (fun θ input => family.shell index bound (θ, input)) θ

public theorem Family.shellImage_measurable (index bound : Nat) (θ : Θ) :
    (Space.pi fun _ : Fin ambient => borel).Measurable (family.shellImage index bound θ) :=
  pair_left_measurable (source := parameter) θ
    ((family.chart index).image_measurable (family.shell_measurable index bound))

/-- A shell's input lands in that shell's image. -/
public theorem Family.map_mem_shellImage {index bound : Nat} {θ : Θ}
    {input : Fin (family.dimension index) → Carrier} (inside : family.shell index bound (θ, input)) :
    family.shellImage index bound θ ((family.chart index).map θ input) :=
  ((family.chart index).image_iff (inputs := fun θ input => family.shell index bound (θ, input))
    (fun _ _ inside => (family.shell_bounded inside).1.1) θ _).mpr ⟨input, inside, rfl⟩

/-- A shell's input lands in no other shell's image. -/
public theorem Family.eq_of_map_mem_shellImage {index bound other otherBound : Nat} {θ : Θ}
    {input : Fin (family.dimension other) → Carrier}
    (inside : family.shell other otherBound (θ, input))
    (landed : family.shellImage index bound θ ((family.chart other).map θ input)) :
    other = index ∧ otherBound = bound := by
  have selectedHere := (family.shell_bounded inside).1
  rcases landed with ⟨member, inverseInside⟩
  have selectedThere := (family.shell_bounded inverseInside).1.2
  rw [(family.chart index).map_inverse θ _ member] at selectedThere
  have same := family.selected_unique selectedHere.2 selectedThere
  subst same
  rw [(family.chart other).inverse_map selectedHere.1] at inverseInside
  refine ⟨rfl, Classical.byContradiction fun different => ?_⟩
  exact Set.disjointed_pairwise _ otherBound bound different inside inverseInside

/-- A shell's contribution is null on a set that none of its inputs reaches. -/
public theorem Family.component_eq_zero {index bound : Nat} {θ : Θ} {set : Set (Fin ambient → Carrier)}
    (setMeasurable : (Space.pi fun _ : Fin ambient => borel).Measurable set)
    (missed : ∀ input, family.shell index bound (θ, input) → ¬set ((family.chart index).map θ input)) :
    family.component index bound θ set = ENNReal.zero := by
  classical
  have preimageMeasurable :=
    section_measurable (family.chart index).map_measurable θ setMeasurable
  rw [family.component_apply, Measure.map_apply _ _ _ setMeasurable,
    Measure.withDensity_apply _ _ preimageMeasurable,
    ← lintegral_indicator _ _ preimageMeasurable]
  have vanishes : ennrealIndicator (Set.preimage ((family.chart index).map θ) set)
      (family.shellDensity index bound θ) = fun _ => ENNReal.zero := by
    funext input
    unfold ennrealIndicator ennrealPiecewise Family.shellDensity ennrealIndicator ennrealPiecewise
    by_cases reached : set ((family.chart index).map θ input)
    · have absent : ¬family.shell index bound (θ, input) := fun inside => missed input inside reached
      simp only [Set.preimage, reached, absent, ↓reduceIte]
    · simp only [Set.preimage, reached, ↓reduceIte]
  rw [vanishes, lintegral_zero]

/-- A shell's contribution puts its whole mass on a set that all its inputs reach. -/
public theorem Family.component_eq_univ {index bound : Nat} {θ : Θ} {set : Set (Fin ambient → Carrier)}
    (setMeasurable : (Space.pi fun _ : Fin ambient => borel).Measurable set)
    (reached : ∀ input, family.shell index bound (θ, input) → set ((family.chart index).map θ input)) :
    family.component index bound θ set = family.component index bound θ Set.univ := by
  classical
  have preimageMeasurable :=
    section_measurable (family.chart index).map_measurable θ setMeasurable
  rw [family.component_apply, Measure.map_apply _ _ _ setMeasurable,
    Measure.map_apply _ _ _ (Space.pi fun _ : Fin ambient => borel).univ, Set.preimage_univ,
    Measure.withDensity_apply _ _ preimageMeasurable,
    Measure.withDensity_apply _ _ (Space.pi fun _ : Fin (family.dimension index) => borel).univ,
    ← lintegral_indicator _ _ preimageMeasurable,
    ← lintegral_indicator _ _ (Space.pi fun _ : Fin (family.dimension index) => borel).univ]
  congr 1
  funext input
  unfold ennrealIndicator ennrealPiecewise Family.shellDensity ennrealIndicator ennrealPiecewise
  by_cases inside : family.shell index bound (θ, input)
  · simp only [Set.preimage, Set.univ, reached input inside, ↓reduceIte]
  · simp only [Set.preimage, Set.univ, inside, ↓reduceIte, ite_self]

/-- A one-chart family's reference: Jacobian-weighted volume on the chart's
domain, pushed through the chart. -/
public theorem Family.single_reference {dimension : Nat} (chart : Chart parameter dimension ambient)
    (θ : Θ) :
    (Family.single chart).reference θ =
      ((volumePi dimension).withDensity (ennrealIndicator (chart.domain θ)
        (fun input => ENNReal.ofReal (chart.jacobian θ input)))).map (chart.map θ)
        (section_measurable chart.map_measurable θ) := by
  classical
  apply Measure.ext
  intro set setMeasurable
  rw [Family.reference_eq_sum, Kernel.sum_apply, Measure.sum_apply _ setMeasurable,
    ENNReal.tsum_eq_of_at_most_one_nonzero _ 0]
  · rw [Kernel.sum_apply, (Family.single chart).sum_component 0 θ]
    have same : (Family.single chart).selectedDensity 0 θ =
        ennrealIndicator (chart.domain θ) (fun input => ENNReal.ofReal (chart.jacobian θ input)) := by
      funext input
      have selected : (Family.single chart).selectedInputs 0 (θ, input) ↔ chart.domain θ input :=
        ⟨fun selected => selected.1, fun inside =>
          ⟨inside, chart.member_map inside, fun _ _ => Or.inr ⟨rfl, Nat.zero_le _⟩⟩⟩
      unfold Family.selectedDensity ennrealIndicator ennrealPiecewise
      by_cases inside : chart.domain θ input
      · simp only [selected.mpr inside, inside, ↓reduceIte]
        rfl
      · simp only [mt selected.mp inside, inside, ↓reduceIte]
    rw [same]
    rfl
  · intro other different
    obtain ⟨later, rfl⟩ := Nat.exists_eq_succ_of_ne_zero different
    rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable]
    have each : ∀ bound, (Family.single chart).component (later + 1) bound θ set = ENNReal.zero :=
      fun bound => (Family.single chart).component_eq_zero setMeasurable
        fun _ inside => ((Family.single chart).shell_bounded inside).1.1.elim
    simp only [each]
    exact ENNReal.tsum_zero

private theorem decode_ne_of_ne {code : Nat} {pair : Nat × Nat}
    (different : code ≠ Countable.Pair.encode pair) : Countable.Pair.decode code ≠ pair := by
  intro same
  apply different
  rw [← same, Countable.Pair.encode_decode]

/-- On the image of a shell, the reference is that shell's contribution alone. -/
public theorem Family.reference_shellImage (index bound : Nat) (θ : Θ) :
    family.reference θ (family.shellImage index bound θ) =
      family.component index bound θ Set.univ := by
  rw [Family.reference, Kernel.sum_apply,
    Measure.sum_apply _ (family.shellImage_measurable index bound θ),
    ENNReal.tsum_eq_of_at_most_one_nonzero _ (Countable.Pair.encode (index, bound))]
  · simp only [Kernel.flatten, Countable.Pair.decode_encode]
    exact family.component_eq_univ (family.shellImage_measurable index bound θ)
      fun _ inside => family.map_mem_shellImage inside
  · intro code different
    simp only [Kernel.flatten]
    apply family.component_eq_zero (family.shellImage_measurable index bound θ)
    intro input inside landed
    have same := family.eq_of_map_mem_shellImage inside landed
    exact decode_ne_of_ne different (Prod.ext same.1 same.2)

/-- The images of every shell, enumerated. -/
@[expose] public def Family.images (θ : Θ) (code : Nat) : Set (Fin ambient → Carrier) :=
  family.shellImage (Countable.Pair.decode code).1 (Countable.Pair.decode code).2 θ

/-- Outside every shell's image, the reference is null. -/
public theorem Family.reference_outside (θ : Θ) :
    family.reference θ (Set.complement (Set.iUnion (family.images θ))) = ENNReal.zero := by
  have measurable : (Space.pi fun _ : Fin ambient => borel).Measurable
      (Set.complement (Set.iUnion (family.images θ))) :=
    (Space.pi _).complement ((Space.pi _).iUnion fun code =>
      family.shellImage_measurable _ _ θ)
  rw [Family.reference, Kernel.sum_apply, Measure.sum_apply _ measurable]
  have each : ∀ code, Kernel.flatten family.component code θ
      (Set.complement (Set.iUnion (family.images θ))) = ENNReal.zero := by
    intro code
    apply family.component_eq_zero measurable
    intro input inside outside
    apply outside
    refine ⟨Countable.Pair.encode ((Countable.Pair.decode code).1, (Countable.Pair.decode code).2), ?_⟩
    simp only [Family.images, Countable.Pair.decode_encode]
    exact family.map_mem_shellImage inside
  simp only [each]
  exact ENNReal.tsum_zero

/-- Every fiber of a family's reference is sigma-finite, by the shell images
and their null remainder. -/
public noncomputable def Family.referenceSigmaFinite (θ : Θ) :
    Measure.SigmaFinite (family.reference θ) :=
  Measure.SigmaFinite.ofCover {
    sets := fun code => match code with
      | 0 => Set.complement (Set.iUnion (family.images θ))
      | code + 1 => family.images θ code
    measurable := fun code => match code with
      | 0 => (Space.pi _).complement ((Space.pi _).iUnion fun code =>
          family.shellImage_measurable _ _ θ)
      | code + 1 => family.shellImage_measurable _ _ θ
    finite := fun code => match code with
      | 0 => by rw [family.reference_outside θ]; exact True.intro
      | code + 1 => by
          change ENNReal.Finite (family.reference θ (family.shellImage _ _ θ))
          rw [family.reference_shellImage]
          exact ((family.component_finite _ _).measure θ).univ_finite
    cover := by
      classical
      apply Set.ext
      intro point
      refine ⟨fun _ => True.intro, fun _ => ?_⟩
      by_cases somewhere : Set.iUnion (family.images θ) point
      · rcases somewhere with ⟨code, inside⟩
        exact ⟨code + 1, inside⟩
      · exact ⟨0, somewhere⟩ }

/-- The standard-Borel presentation of the ambient coordinates. -/
public noncomputable def ambientStandardBorel (ambient : Nat) :
    StandardBorel (Space.pi fun _ : Fin ambient => borel) :=
  StandardBorel.piOfNatInjection Fin.val (fun _ _ same => Fin.ext same)
    (fun _ => StandardBorel.real)

/-- A law that a family's reference covers at every parameter has a jointly
measurable density against it. -/
public noncomputable def Family.derivative (law : Kernel parameter (Space.pi fun _ : Fin ambient => borel))
    (lawFinite : IsSFinite law)
    (covers : ∀ θ, Measure.AbsolutelyContinuous (law θ) (family.reference θ)) :
    RadonNikodymDerivative law family.reference :=
  RadonNikodymDerivative.ofStandardBorelSigmaFinite (ambientStandardBorel ambient) lawFinite
    family.referenceSFinite family.referenceSigmaFinite covers

end

end Problib.Measure.Kernel.Chart
