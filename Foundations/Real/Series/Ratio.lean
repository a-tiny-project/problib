module

public import Foundations.Real.Series.Basis

set_option autoImplicit false

/-!
# Extended nonnegative real density ratio

Defines the density ratio function `densityRatio` on extended nonnegative reals,
handling infinite and zero reference values, and proves reconstruction identities
for factorable products.
-/

namespace Foundations.Real.ENNReal

/-- Density ratio of two extended nonnegative reals, defined by supremum over rational
lower bounds for finite positive reference values and handling zero and infinity explicitly. -/
@[expose] public noncomputable def densityRatio (target reference : ENNReal) : ENNReal := by
  classical
  exact if reference = zero then zero
    else if reference = top then if target = zero then zero else one
    else iSup (fun index =>
      if le (mul reference (rationalBasis index)) target then rationalBasis index else zero)

/-- Cancellation of multiplication by a finite positive reference in the density ratio. -/
public theorem densityRatio_mul_of_finite {reference : ENNReal} (finite : Finite reference)
    (nonzero : reference ≠ zero) (value : ENNReal) : densityRatio (mul reference value) reference = value := by
  classical
  rw [densityRatio, if_neg nonzero, if_neg (finiteIffNeTop.mp finite)]
  let terms := fun index =>
    if le (mul reference (rationalBasis index)) (mul reference value) then rationalBasis index else zero
  have upper : le (iSup terms) value := by
    apply iSupLe
    intro index
    by_cases included : le (mul reference (rationalBasis index)) (mul reference value)
    · simp only [terms, if_pos included]
      exact (mulLeMulLeftIff finite (zeroLtIffNeZero.mpr nonzero)).mp included
    · simpa only [terms, if_neg included] using zeroLe value
  apply leAntisymm upper
  apply Classical.byContradiction
  intro notIncluded
  rcases existsRationalBasisBetween ⟨upper, notIncluded⟩ with ⟨index, above, below⟩
  have included : le (mul reference (rationalBasis index)) (mul reference value) :=
    mulLeMulLeft below.1 reference
  have term : terms index = rationalBasis index := by
    simp only [terms, if_pos included]
  have lower := leISup terms index
  rw [term] at lower
  exact above.2 lower

/-- Reconstruction of a factorable product when multiplying by the reference value. -/
public theorem mul_densityRatio (reference value : ENNReal) :
    mul reference (densityRatio (mul reference value) reference) = mul reference value := by
  classical
  by_cases referenceZero : reference = zero
  · rw [referenceZero, zeroMul, zeroMul]
  · by_cases referenceTop : reference = top
    · by_cases productZero : mul reference value = zero
      · rw [densityRatio, if_neg referenceZero, if_pos referenceTop, if_pos productZero,
          mulZero, productZero]
      · have valueNonzero : value ≠ zero := by
          intro equal
          exact productZero (equal ▸ mulZero reference)
        rw [densityRatio, if_neg referenceZero, if_pos referenceTop, if_neg productZero,
          mulOne, referenceTop, topMulOfNeZero valueNonzero]
    · rw [densityRatio_mul_of_finite (finiteIffNeTop.mpr referenceTop) referenceZero value]

end Foundations.Real.ENNReal
