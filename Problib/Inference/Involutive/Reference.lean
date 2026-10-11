module

public import Problib.Inference.Involutive
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

/-!
# Involutions that change their reference

An involution `F` need not preserve a reference `ρ`. When it changes it by a
Jacobian, `F∗ρ = ρ.withDensity j` with `j (F z) · j z = 1`, the symmetrized
reference `ρ + F∗ρ` is preserved by `F` (`symmetrized_map_involution`) and
equals `ρ.withDensity (1 + j)`. A law with density `m` against `ρ` then has
Green's density `m / (1 + j)` against it (`greenDensity_represents`), so
`involutive_invariant_of_reference` applies with no reversibility premise.

The strict test on Green's density compares `m z` with `j z · m (F z)`
(`involutiveAccept_greenDensity`): the common factor `1 / (1 + j z)` scales out
of the strict comparison.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable ofReal_mul measurable_mul
  measurable_add inverse_measurable uniform01)

universe u v
variable {α : Type u} {space : Space α}

public section

/-- Green's density: the mass divided by one plus the Jacobian. -/
@[expose] noncomputable def greenDensity (jacobian mass : α → Carrier) (point : α) : Carrier :=
  Dedekind.mul (mass point) (Dedekind.inverse (Dedekind.add Dedekind.one (jacobian point)))

theorem greenDensity_measurable {jacobian mass : α → Carrier}
    (jacobianMeasurable : MeasurableMap space borel jacobian)
    (massMeasurable : MeasurableMap space borel mass) :
    MeasurableMap space borel (greenDensity jacobian mass) :=
  measurable_mul massMeasurable
    (MeasurableMap.comp inverse_measurable
      (measurable_add (MeasurableMap.constant _ borel Dedekind.one) jacobianMeasurable))

private theorem one_add_positive {value : Carrier}
    (nonnegative : Dedekind.le Dedekind.zero value) :
    Dedekind.lt Dedekind.zero (Dedekind.add Dedekind.one value) := by
  have atLeast : Dedekind.le Dedekind.one (Dedekind.add Dedekind.one value) := by
    have shifted := (Dedekind.add_le_add_left_iff (left := Dedekind.zero) (right := value)
      (shift := Dedekind.one)).mpr nonnegative
    rwa [Dedekind.add_zero] at shifted
  exact Dedekind.lt_of_lt_of_le Dedekind.one_positive atLeast

/-- A law with density `mass` against a reference that the involution changes
by `jacobian` has Green's density against the symmetrized reference. -/
theorem greenDensity_represents (reference : Measure space)
    {involution : α → α} (involutionMeasurable : MeasurableMap space space involution)
    {jacobian mass : α → Carrier}
    (jacobianMeasurable : MeasurableMap space borel jacobian)
    (massMeasurable : MeasurableMap space borel mass)
    (jacobianNonnegative : ∀ point, Dedekind.le Dedekind.zero (jacobian point))
    (massNonnegative : ∀ point, Dedekind.le Dedekind.zero (mass point))
    (change : reference.map involution involutionMeasurable =
      reference.withDensity (fun point => ENNReal.ofReal (jacobian point))) :
    reference.withDensity (fun point => ENNReal.ofReal (mass point)) =
      (Measure.add reference (reference.map involution involutionMeasurable)).withDensity
        (fun point => ENNReal.ofReal (greenDensity jacobian mass point)) := by
  have jacobianWeight : ENNRealMeasurable space (fun point => ENNReal.ofReal (jacobian point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable jacobianMeasurable
  have greenWeight : ENNRealMeasurable space
      (fun point => ENNReal.ofReal (greenDensity jacobian mass point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (greenDensity_measurable jacobianMeasurable massMeasurable)
  have unitWeight : ENNRealMeasurable space (fun _ : α => ENNReal.one) :=
    ENNRealMeasurable.constant _ _
  have symmetrized : Measure.add reference (reference.map involution involutionMeasurable) =
      reference.withDensity
        (fun point => ENNReal.add ENNReal.one (ENNReal.ofReal (jacobian point))) := by
    rw [change, Measure.withDensity_add _ unitWeight jacobianWeight, Measure.withDensity_one]
  rw [symmetrized, Measure.withDensity_withDensity _
    (ENNRealMeasurable.add unitWeight jacobianWeight) greenWeight]
  refine congrArg reference.withDensity (funext fun point => ?_)
  have positive := one_add_positive (jacobianNonnegative point)
  have inverseNonnegative := (Dedekind.inverse_of_positive_positive positive).1
  unfold greenDensity
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add Dedekind.one_nonnegative
      (jacobianNonnegative point),
    ← ofReal_mul positive.1
      (Dedekind.mul_nonnegative (massNonnegative point) inverseNonnegative)]
  congr 1
  rw [Dedekind.mul_comm (mass point), ← Dedekind.mul_assoc,
    Dedekind.mul_inverse_cancel_of_positive positive, Dedekind.one_mul]

/-- The strict test on Green's density compares the mass at a point with the
Jacobian times the mass at its image. -/
theorem involutiveAccept_greenDensity {β : Type v} {involution : α × β → α × β}
    {jacobian mass : α × β → Carrier} (point : α × β)
    (jacobianNonnegative : Dedekind.le Dedekind.zero (jacobian point))
    (reciprocal : Dedekind.mul (jacobian (involution point)) (jacobian point) = Dedekind.one) :
    involutiveAccept involution (greenDensity jacobian mass) point =
      metropolisAccept (fun weight : Carrier => weight)
        (mass point, Dedekind.mul (jacobian point) (mass (involution point))) := by
  let scale := Dedekind.inverse (Dedekind.add Dedekind.one (jacobian point))
  have positive := one_add_positive jacobianNonnegative
  have scalePositive : Dedekind.lt Dedekind.zero scale :=
    Dedekind.inverse_of_positive_positive positive
  have imageSum : Dedekind.mul (Dedekind.add Dedekind.one (jacobian (involution point)))
      (Dedekind.mul (jacobian point) scale) = Dedekind.one := by
    calc Dedekind.mul (Dedekind.add Dedekind.one (jacobian (involution point)))
          (Dedekind.mul (jacobian point) scale)
        = Dedekind.add (Dedekind.mul (jacobian point) scale)
            (Dedekind.mul (Dedekind.mul (jacobian (involution point)) (jacobian point))
              scale) := by
          rw [Dedekind.add_mul, Dedekind.one_mul, Dedekind.mul_assoc]
      _ = Dedekind.mul (Dedekind.add (jacobian point) Dedekind.one) scale := by
          rw [reciprocal, Dedekind.one_mul, Dedekind.add_mul, Dedekind.one_mul]
      _ = Dedekind.one := by
          rw [Dedekind.add_comm]
          exact Dedekind.mul_inverse_cancel_of_positive positive
  have imageNonzero :
      Dedekind.add Dedekind.one (jacobian (involution point)) ≠ Dedekind.zero := by
    intro vanished
    rw [vanished, Dedekind.zero_mul] at imageSum
    exact Dedekind.one_ne_zero imageSum.symm
  have imageScale : Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point))) =
      Dedekind.mul (jacobian point) scale := by
    calc Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point)))
        = Dedekind.mul (Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point))))
            Dedekind.one := (Dedekind.mul_one _).symm
      _ = Dedekind.mul (Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point))))
            (Dedekind.mul (Dedekind.add Dedekind.one (jacobian (involution point)))
              (Dedekind.mul (jacobian point) scale)) := by rw [imageSum]
      _ = Dedekind.mul (jacobian point) scale := by
          rw [← Dedekind.mul_assoc, Dedekind.inverse_mul_cancel imageNonzero, Dedekind.one_mul]
  unfold involutiveAccept metropolisAccept
  refine congrArg uniform01 (funext fun draw => propext ?_)
  change Dedekind.lt (Dedekind.mul draw.val (Dedekind.mul (mass point) scale))
      (Dedekind.mul (mass (involution point))
        (Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point))))) ↔
    Dedekind.lt (Dedekind.mul draw.val (mass point))
      (Dedekind.mul (jacobian point) (mass (involution point)))
  have drawn : Dedekind.mul draw.val (Dedekind.mul (mass point) scale) =
      Dedekind.mul scale (Dedekind.mul draw.val (mass point)) := by
    rw [← Dedekind.mul_assoc, Dedekind.mul_comm]
  have proposed : Dedekind.mul (mass (involution point))
        (Dedekind.inverse (Dedekind.add Dedekind.one (jacobian (involution point)))) =
      Dedekind.mul scale (Dedekind.mul (jacobian point) (mass (involution point))) := by
    rw [imageScale, ← Dedekind.mul_assoc, Dedekind.mul_comm, Dedekind.mul_comm (mass _)]
  rw [drawn, proposed]
  exact Dedekind.mul_lt_mul_left_iff scalePositive

end
end Problib.Inference
