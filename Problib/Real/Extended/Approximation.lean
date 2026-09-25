module

public import Problib.Real.Extended.Supremum

namespace Problib.Real.ENNReal

set_option autoImplicit false

@[expose] public noncomputable def half : ENNReal → ENNReal
  | .finite value => .finite (NNReal.half value)
  | .top => top

public theorem half_finite {value : ENNReal} :
    Finite (half value) ↔ Finite value := by
  cases value with
  | finite _ => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | top => exact ⟨False.elim, False.elim⟩

public theorem half_add_half (value : ENNReal) :
    add (half value) (half value) = value := by
  cases value with
  | top => rfl
  | finite underlying =>
      exact congrArg finite (NNReal.half_add_half underlying)

public theorem half_positive {value : ENNReal} (positive : lt zero value) :
    lt zero (half value) := by
  cases value with
  | top => exact zero_lt_top
  | finite underlying => exact NNReal.half_positive positive

public theorem half_ne_zero {value : ENNReal} (nonzero : value ≠ zero) :
    half value ≠ zero :=
  zero_lt_iff_ne_zero.mp (half_positive (zero_lt_iff_ne_zero.mpr nonzero))

public theorem one_positive : lt zero one :=
  zero_lt_iff_ne_zero.mpr one_ne_zero

public theorem lt_add_of_finite_of_positive {value error : ENNReal}
    (valueFinite : Finite value) (errorPositive : lt zero error) :
    lt value (add value error) := by
  rcases exists_finite_of_finite valueFinite with ⟨valueValue, rfl⟩
  cases error with
  | top =>
      exact ⟨le_top _, fun reverse => reverse⟩
  | finite errorValue =>
      have shifted := (NNReal.add_lt_add_left_iff
        (left := NNReal.zero) (right := errorValue)
        (shift := valueValue)).mpr errorPositive
      change NNReal.lt valueValue (NNReal.add valueValue errorValue)
      simpa only [NNReal.add_zero] using shifted

public theorem half_lt_self_of_positive_of_finite {value : ENNReal}
    (positive : lt zero value) (finiteValue : Finite value) :
    lt (half value) value := by
  have halfFiniteValue := half_finite.mpr finiteValue
  have shifted := lt_add_of_finite_of_positive halfFiniteValue
    (half_positive positive)
  rw [half_add_half value] at shifted
  exact shifted

public theorem le_of_forall_positive_le_add {left right : ENNReal}
    (approaches : ∀ error : ENNReal, lt zero error →
      le left (add right error)) :
    le left right := by
  cases right with
  | top => exact le_top left
  | finite rightValue =>
      cases left with
      | top => exact False.elim (approaches one one_positive)
      | finite leftValue =>
          apply NNReal.le_of_forall_positive_le_add
          intro error errorPositive
          exact approaches (finite error) errorPositive

public theorem exists_less_than_infimum_add {set : ENNReal → Prop}
    {error : ENNReal} (infimumFinite : Finite (infimum set))
    (errorPositive : lt zero error) :
    ∃ value, set value ∧ lt value (add (infimum set) error) :=
  exists_less_of_infimum_lt
    (lt_add_of_finite_of_positive infimumFinite errorPositive)

/-- For a nonempty set with finite supremum and strictly positive error, some
element approximates the supremum within that error. -/
public theorem exists_supremum_le_add {set : ENNReal → Prop}
    (nonempty : ∃ value, set value) (supremumFinite : Finite (supremum set))
    {error : ENNReal} (errorPositive : lt zero error) :
    ∃ value, set value ∧ le (supremum set) (add value error) := by
  classical
  apply Classical.byContradiction
  intro missing
  have bound : le (supremum (image (add error) set)) (supremum set) := by
    apply supremum_le
    rintro value ⟨before, member, rfl⟩
    rw [add_comm error before]
    exact (le_total (supremum set) (add before error)).resolve_left
      (fun included => missing ⟨before, member, included⟩)
  rw [← add_supremum error nonempty, add_comm error (supremum set)] at bound
  exact (lt_add_of_finite_of_positive supremumFinite errorPositive).2 bound

end Problib.Real.ENNReal
