module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Real.Box

/-! # Charts and chart families

A reference measure that follows a parameter is assembled from charts. A chart
gives, at every parameter, an injective map from a region of `dimension`
coordinates into `ambient` coordinates, together with what a reference built
from it must read back: the Jacobian that weights volume, an exact test for
membership in the image, and an inverse on the image. Every component is jointly
measurable in the parameter and the point, so the references built from charts
are kernels.

A family is countably many charts, each with its own dimension. The chart at
one index may have an empty region, which is how a finite family pads its tail.

Nothing here asks for smoothness. The kernel built from a family, its
s-finiteness and its sigma-finite fibers use only the measurable structure.
Smoothness enters where the kernel is compared with Hausdorff measure.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real (borel Carrier)

public section

universe u

variable {Θ : Type u} {parameter : Space Θ}

/-- A measurable family, over parameters, of injective maps from regions of
`dimension` coordinates into `ambient` coordinates. Each carries a Jacobian, an
exact membership test for its image, and an inverse on that image. -/
public structure Chart (parameter : Space Θ) (dimension ambient : Nat) where
  domain : Θ → Set (Fin dimension → Carrier)
  map : Θ → (Fin dimension → Carrier) → Fin ambient → Carrier
  jacobian : Θ → (Fin dimension → Carrier) → Carrier
  member : Θ → Set (Fin ambient → Carrier)
  inverse : Θ → (Fin ambient → Carrier) → Fin dimension → Carrier
  domain_measurable :
    (Space.product parameter (Space.pi fun _ : Fin dimension => borel)).Measurable
      (fun pair => domain pair.1 pair.2)
  map_measurable :
    MeasurableMap (Space.product parameter (Space.pi fun _ : Fin dimension => borel))
      (Space.pi fun _ : Fin ambient => borel) (fun pair => map pair.1 pair.2)
  jacobian_measurable :
    MeasurableMap (Space.product parameter (Space.pi fun _ : Fin dimension => borel))
      borel (fun pair => jacobian pair.1 pair.2)
  member_measurable :
    (Space.product parameter (Space.pi fun _ : Fin ambient => borel)).Measurable
      (fun pair => member pair.1 pair.2)
  inverse_measurable :
    MeasurableMap (Space.product parameter (Space.pi fun _ : Fin ambient => borel))
      (Space.pi fun _ : Fin dimension => borel) (fun pair => inverse pair.1 pair.2)
  injective : ∀ θ first second, domain θ first → domain θ second →
    map θ first = map θ second → first = second
  member_iff : ∀ θ point, member θ point ↔ ∃ input, domain θ input ∧ map θ input = point
  inverse_domain : ∀ θ point, member θ point → domain θ (inverse θ point)
  map_inverse : ∀ θ point, member θ point → map θ (inverse θ point) = point

namespace Chart

variable {dimension ambient : Nat} (chart : Chart parameter dimension ambient)

/-- A chart's image holds every point it maps to. -/
public theorem member_map {θ : Θ} {input : Fin dimension → Carrier}
    (inside : chart.domain θ input) : chart.member θ (chart.map θ input) :=
  (chart.member_iff θ _).mpr ⟨input, inside, rfl⟩

/-- The inverse undoes the chart on its domain. -/
public theorem inverse_map {θ : Θ} {input : Fin dimension → Carrier}
    (inside : chart.domain θ input) : chart.inverse θ (chart.map θ input) = input :=
  chart.injective θ _ _ (chart.inverse_domain θ _ (chart.member_map inside)) inside
    (chart.map_inverse θ _ (chart.member_map inside))

/-- The image of a region of inputs, read through the inverse: a point is in it
when the chart's image holds it and its inverse lies in the region. -/
@[expose] public def image (inputs : Θ → Set (Fin dimension → Carrier)) (θ : Θ) :
    Set (Fin ambient → Carrier) :=
  fun point => chart.member θ point ∧ inputs θ (chart.inverse θ point)

/-- For a region inside the domain, the image holds exactly the points the
chart maps the region to. -/
public theorem image_iff {inputs : Θ → Set (Fin dimension → Carrier)}
    (within : ∀ θ input, inputs θ input → chart.domain θ input) (θ : Θ)
    (point : Fin ambient → Carrier) :
    chart.image inputs θ point ↔ ∃ input, inputs θ input ∧ chart.map θ input = point := by
  constructor
  · rintro ⟨member, inside⟩
    exact ⟨chart.inverse θ point, inside, chart.map_inverse θ point member⟩
  · rintro ⟨input, inside, rfl⟩
    refine ⟨chart.member_map (within θ input inside), ?_⟩
    rw [chart.inverse_map (within θ input inside)]
    exact inside

/-- The image of a jointly measurable region is jointly measurable. -/
public theorem image_measurable {inputs : Θ → Set (Fin dimension → Carrier)}
    (inputsMeasurable :
      (Space.product parameter (Space.pi fun _ : Fin dimension => borel)).Measurable
        (fun pair => inputs pair.1 pair.2)) :
    (Space.product parameter (Space.pi fun _ : Fin ambient => borel)).Measurable
      (fun pair => chart.image inputs pair.1 pair.2) :=
  (Space.product parameter _).inter chart.member_measurable
    (Space.pair_measurable (Space.first_measurable _ _) chart.inverse_measurable inputsMeasurable)

/-- The chart with nothing in its domain. -/
@[expose] public noncomputable def empty (parameter : Space Θ) (dimension ambient : Nat) :
    Chart parameter dimension ambient where
  domain := fun _ => Set.empty
  map := fun _ _ _ => Dedekind.zero
  jacobian := fun _ _ => Dedekind.zero
  member := fun _ => Set.empty
  inverse := fun _ _ _ => Dedekind.zero
  domain_measurable := (Space.product parameter _).empty
  map_measurable := MeasurableMap.constant _ _ _
  jacobian_measurable := MeasurableMap.constant _ _ _
  member_measurable := (Space.product parameter _).empty
  inverse_measurable := MeasurableMap.constant _ _ _
  injective := fun _ _ _ inside => inside.elim
  member_iff := fun _ _ => ⟨False.elim, fun ⟨_, inside, _⟩ => inside.elim⟩
  inverse_domain := fun _ _ member => member.elim
  map_inverse := fun _ _ member => member.elim

/-- Countably many charts, each with its own dimension. -/
public structure Family (parameter : Space Θ) (ambient : Nat) where
  dimension : Nat → Nat
  chart : (index : Nat) → Chart parameter (dimension index) ambient

/-- One chart at index zero, padded by empty charts. -/
@[expose] public noncomputable def Family.single (chart : Chart parameter dimension ambient) :
    Family parameter ambient where
  dimension := fun _ => dimension
  chart := fun index => match index with
    | 0 => chart
    | _ + 1 => empty parameter dimension ambient

end Chart

end

end Problib.Measure.Kernel
