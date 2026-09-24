module

public import Problib.Real.Series.Basis

set_option autoImplicit false

/-!
# Extended nonnegative real density ratio

Defines the density ratio function `densityRatio` on extended nonnegative reals,
handling infinite and zero reference values, and proves reconstruction identities
for factorable products.
-/

namespace Problib.Real.ENNReal

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
  rw [densityRatio, if_neg nonzero, if_neg (finite_iff_ne_top.mp finite)]
  let terms := fun index =>
    if le (mul reference (rationalBasis index)) (mul reference value) then rationalBasis index else zero
  have upper : le (iSup terms) value := by
    apply iSup_le
    intro index
    by_cases included : le (mul reference (rationalBasis index)) (mul reference value)
    · simp only [terms, if_pos included]
      exact (mul_le_mul_left_iff finite (zero_lt_iff_ne_zero.mpr nonzero)).mp included
    · simpa only [terms, if_neg included] using zero_le value
  apply le_antisymm upper
  apply Classical.byContradiction
  intro notIncluded
  rcases exists_rationalBasis_between ⟨upper, notIncluded⟩ with ⟨index, above, below⟩
  have included : le (mul reference (rationalBasis index)) (mul reference value) :=
    mul_le_mul_left below.1 reference
  have term : terms index = rationalBasis index := by
    simp only [terms, if_pos included]
  have lower := le_iSup terms index
  rw [term] at lower
  exact above.2 lower

/-- Reconstruction of a factorable product when multiplying by the reference value. -/
public theorem mul_densityRatio (reference value : ENNReal) :
    mul reference (densityRatio (mul reference value) reference) = mul reference value := by
  classical
  by_cases referenceZero : reference = zero
  · rw [referenceZero, zero_mul, zero_mul]
  · by_cases referenceTop : reference = top
    · by_cases productZero : mul reference value = zero
      · rw [densityRatio, if_neg referenceZero, if_pos referenceTop, if_pos productZero,
          mul_zero, productZero]
      · have valueNonzero : value ≠ zero := by
          intro equal
          exact productZero (equal ▸ mul_zero reference)
        rw [densityRatio, if_neg referenceZero, if_pos referenceTop, if_neg productZero,
          mul_one, referenceTop, top_mul_of_ne_zero valueNonzero]
    · rw [densityRatio_mul_of_finite (finite_iff_ne_top.mpr referenceTop) referenceZero value]

end Problib.Real.ENNReal
