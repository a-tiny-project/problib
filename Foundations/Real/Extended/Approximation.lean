module

public import Foundations.Real.Extended.Supremum

namespace Foundations.Real.ENNReal

set_option autoImplicit false

@[expose] public noncomputable def half : ENNReal → ENNReal
  | .finite value => .finite (NNReal.half value)
  | .top => top

public theorem halfFinite {value : ENNReal} :
    Finite (half value) ↔ Finite value := by
  cases value with
  | finite _ => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
  | top => exact ⟨False.elim, False.elim⟩

public theorem halfAddHalf (value : ENNReal) :
    add (half value) (half value) = value := by
  cases value with
  | top => rfl
  | finite underlying =>
      exact congrArg finite (NNReal.halfAddHalf underlying)

public theorem halfPositive {value : ENNReal} (positive : lt zero value) :
    lt zero (half value) := by
  cases value with
  | top => exact zeroLtTop
  | finite underlying => exact NNReal.halfPositive positive

public theorem halfNeZero {value : ENNReal} (nonzero : value ≠ zero) :
    half value ≠ zero :=
  zeroLtIffNeZero.mp (halfPositive (zeroLtIffNeZero.mpr nonzero))

public theorem onePositive : lt zero one :=
  zeroLtIffNeZero.mpr oneNeZero

public theorem ltAddOfFiniteOfPositive {value error : ENNReal}
    (valueFinite : Finite value) (errorPositive : lt zero error) :
    lt value (add value error) := by
  rcases existsFiniteOfFinite valueFinite with ⟨valueValue, rfl⟩
  cases error with
  | top =>
      exact ⟨leTop _, fun reverse => reverse⟩
  | finite errorValue =>
      have shifted := (NNReal.addLtAddLeftIff
        (left := NNReal.zero) (right := errorValue)
        (shift := valueValue)).mpr errorPositive
      change NNReal.lt valueValue (NNReal.add valueValue errorValue)
      simpa only [NNReal.addZero] using shifted

public theorem halfLtSelfOfPositiveOfFinite {value : ENNReal}
    (positive : lt zero value) (finiteValue : Finite value) :
    lt (half value) value := by
  have halfFiniteValue := halfFinite.mpr finiteValue
  have shifted := ltAddOfFiniteOfPositive halfFiniteValue
    (halfPositive positive)
  rw [halfAddHalf value] at shifted
  exact shifted

public theorem leOfForallPositiveLeAdd {left right : ENNReal}
    (approaches : ∀ error : ENNReal, lt zero error →
      le left (add right error)) :
    le left right := by
  cases right with
  | top => exact leTop left
  | finite rightValue =>
      cases left with
      | top => exact False.elim (approaches one onePositive)
      | finite leftValue =>
          apply NNReal.leOfForallPositiveLeAdd
          intro error errorPositive
          exact approaches (finite error) errorPositive

public theorem existsLessThanInfimumAdd {set : ENNReal → Prop}
    {error : ENNReal} (infimumFinite : Finite (infimum set))
    (errorPositive : lt zero error) :
    ∃ value, set value ∧ lt value (add (infimum set) error) :=
  existsLessOfInfimumLt
    (ltAddOfFiniteOfPositive infimumFinite errorPositive)

/-- For a nonempty set with finite supremum and strictly positive error, some
element approximates the supremum within that error. -/
public theorem existsSupremumLeAdd {set : ENNReal → Prop}
    (nonempty : ∃ value, set value) (supremumFinite : Finite (supremum set))
    {error : ENNReal} (errorPositive : lt zero error) :
    ∃ value, set value ∧ le (supremum set) (add value error) := by
  classical
  apply Classical.byContradiction
  intro missing
  have bound : le (supremum (image (add error) set)) (supremum set) := by
    apply supremumLe
    rintro value ⟨before, member, rfl⟩
    rw [addComm error before]
    exact (leTotal (supremum set) (add before error)).resolve_left
      (fun included => missing ⟨before, member, included⟩)
  rw [← addSupremum error nonempty, addComm error (supremum set)] at bound
  exact (ltAddOfFiniteOfPositive supremumFinite errorPositive).2 bound

end Foundations.Real.ENNReal
