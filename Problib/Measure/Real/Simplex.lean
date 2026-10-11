module

public import Problib.Measure.Real.Pi
public import Problib.Measure.Real.Order
public import Problib.Measure.Real.Arithmetic
public import Problib.Algebra.Sum

/-! The simplex reference measure.

The coordinates of a finite real vector add with the generic vector sum at the
real additive laws, `additiveLaws.finSum`, and `finTail` drops the leading
coordinate. The free coordinates of the open simplex are the vectors with
positive coordinates whose sum is below one (`simplexRegion`).
`simplexPoint` puts the leftover `1 - Σv` in front of them, so every image point
has positive coordinates summing to one. `simplex` is Lebesgue measure on the
free region, pushed forward by `simplexPoint`: the reference measure of the open
simplex in `dimension + 1` coordinates. Its integrals are Lebesgue integrals
over the free region (`lintegral_simplex`).

The leftover is the leading coordinate because product Lebesgue measure
prepends one coordinate per dimension (`volumePi_succ`). A recursion over the
free coordinates then peels them in the order the measure does.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

public section

/-- Drop the leading coordinate. -/
@[expose] public def finTail (dimension : Nat) (point : Fin (dimension + 1) → Carrier) :
    Fin dimension → Carrier :=
  fun index => point index.succ

/-- Dropping the leading coordinate is measurable. -/
public theorem finTail_measurable (dimension : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin (dimension + 1) => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (finTail dimension) :=
  Space.pi_measurable (fun index =>
    Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) index.succ)

/-- Summing the coordinates of a finite real vector is measurable. -/
public theorem finSum_measurable : (dimension : Nat) →
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel)) borel
      (additiveLaws.finSum dimension)
  | 0 => MeasurableMap.constant _ borel zero
  | dimension + 1 => measurable_add
      (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) 0)
      (MeasurableMap.comp (finSum_measurable dimension) (finTail_measurable dimension))

/-- Nonnegative coordinates have a nonnegative sum. -/
public theorem finSum_nonnegative : (dimension : Nat) → (point : Fin dimension → Carrier) →
    (∀ index, le zero (point index)) → le zero (additiveLaws.finSum dimension point)
  | 0, _, _ => le_refl zero
  | dimension + 1, point, nonnegative =>
      add_nonnegative (nonnegative 0) (finSum_nonnegative dimension
        (finTail dimension point) (fun index => nonnegative index.succ))

/-- Positive coordinates have a positive sum. -/
public theorem finSum_positive (dimension : Nat) {point : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (point index)) :
    lt zero (additiveLaws.finSum (dimension + 1) point) := by
  have rest := finSum_nonnegative dimension (finTail dimension point)
    (fun index => (positive index.succ).1)
  have sum := add_lt_add_le (positive 0) rest
  rwa [add_zero] at sum

/-- The vectors whose coordinates are all positive form a measurable set. -/
private theorem positive_measurable : (dimension : Nat) →
    (Space.pi (fun _ : Fin dimension => borel)).Measurable
      (fun point : Fin dimension → Carrier => ∀ index, lt zero (point index))
  | 0 => by
      have all : (fun point : Fin 0 → Carrier => ∀ index, lt zero (point index)) = Set.univ :=
        Set.ext (fun _ => ⟨fun _ => True.intro, fun _ index => Fin.elim0 index⟩)
      rw [all]
      exact Space.univ _
  | dimension + 1 => by
      have split : (fun point : Fin (dimension + 1) → Carrier => ∀ index, lt zero (point index)) =
          Set.inter (fun point => lt zero (point 0))
            (Set.preimage (finTail dimension)
              (fun point : Fin dimension → Carrier => ∀ index, lt zero (point index))) :=
        Set.ext (fun point => ⟨fun all => ⟨all 0, fun index => all index.succ⟩,
          fun both index => Fin.cases both.1 both.2 index⟩)
      rw [split]
      exact Space.inter _
        (measurable_lt (MeasurableMap.constant _ borel zero)
          (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) 0))
        (finTail_measurable dimension (positive_measurable dimension))

/-- The free coordinates of the open simplex: positive coordinates whose sum is
below one. -/
@[expose] public def simplexRegion (dimension : Nat) : Set (Fin dimension → Carrier) :=
  fun point => (∀ index, lt zero (point index)) ∧ lt (additiveLaws.finSum dimension point) one

public theorem simplexRegion_measurable (dimension : Nat) :
    (Space.pi (fun _ : Fin dimension => borel)).Measurable (simplexRegion dimension) :=
  Space.inter _ (positive_measurable dimension)
    (measurable_lt (finSum_measurable dimension) (MeasurableMap.constant _ borel one))

/-- The simplex point with the given free coordinates: the leftover `1 - Σv`,
followed by the free coordinates. -/
@[expose] public noncomputable def simplexPoint (dimension : Nat) (point : Fin dimension → Carrier) :
    Fin (dimension + 1) → Carrier :=
  finCons dimension (sub one (additiveLaws.finSum dimension point), point)

public theorem simplexPoint_measurable (dimension : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin (dimension + 1) => borel)) (simplexPoint dimension) :=
  MeasurableMap.comp (finCons_measurable dimension)
    (Space.pair_measurable
      (measurable_sub (MeasurableMap.constant _ borel one) (finSum_measurable dimension))
      (MeasurableMap.identity _))

/-- A simplex point's coordinates sum to one. -/
public theorem finSum_simplexPoint (dimension : Nat) (point : Fin dimension → Carrier) :
    additiveLaws.finSum (dimension + 1) (simplexPoint dimension point) = one :=
  sub_add_cancel one (additiveLaws.finSum dimension point)

/-- A free point of the open simplex gives a simplex point with positive
coordinates. -/
public theorem simplexPoint_positive {dimension : Nat} {point : Fin dimension → Carrier}
    (member : simplexRegion dimension point) (index : Fin (dimension + 1)) :
    lt zero (simplexPoint dimension point index) :=
  Fin.cases (motive := fun index => lt zero (simplexPoint dimension point index))
    (sub_positive_iff.mpr member.2) member.1 index

/-- Lebesgue measure on the open simplex in `dimension + 1` coordinates: volume
on the free region, carried by `simplexPoint`. -/
@[expose] public noncomputable def simplex (dimension : Nat) :
    Measure (Space.pi (fun _ : Fin (dimension + 1) => borel)) :=
  ((volumePi dimension).restrict (simplexRegion dimension)).map (simplexPoint dimension)
    (simplexPoint_measurable dimension)

@[expose] public noncomputable def simplexSFinite (dimension : Nat) :
    Measure.SFinite (simplex dimension) :=
  ((volumePiSFinite dimension).restrict (simplexRegion_measurable dimension)).map
    (simplexPoint dimension) (simplexPoint_measurable dimension)

/-- Almost every point of the simplex has positive coordinates. -/
public theorem simplex_ae_positive (dimension : Nat) :
    (simplex dimension).AE (fun point => ∀ index, lt zero (point index)) := by
  unfold simplex
  rw [Measure.ae_map_iff _ _ (positive_measurable (dimension + 1))]
  exact ((volumePi dimension).ae_restrict_mem (simplexRegion_measurable dimension)).mono
    (fun _ member => simplexPoint_positive member)

/-- Integrals against the simplex are Lebesgue integrals over the free region. -/
public theorem lintegral_simplex (dimension : Nat)
    {integrand : (Fin (dimension + 1) → Carrier) → ENNReal}
    (measurable : ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel))
      integrand) :
    lintegral (simplex dimension) integrand =
      lintegral (volumePi dimension) (ennrealIndicator (simplexRegion dimension)
        (fun point => integrand (simplexPoint dimension point))) := by
  unfold simplex
  rw [lintegral_map _ _ _ measurable,
    lintegral_indicator _ _ (simplexRegion_measurable dimension)]

end

end Problib.Measure.Real
