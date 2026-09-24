module

public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere

set_option autoImplicit false

namespace Problib.Measure.Measure

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- Semiproducts of s-finite kernels that agree almost everywhere under the base
measure are equal. -/
public theorem semiproduct_congr_ae (measure : Measure source)
    {left right : Kernel source target}
    (leftFinite : Kernel.IsSFinite left) (rightFinite : Kernel.IsSFinite right)
    (equal : measure.AEEq (fun input => left input) (fun input => right input)) :
    semiproduct measure left leftFinite = semiproduct measure right rightFinite := by
  apply Measure.ext
  intro set measurable
  rw [semiproduct_apply _ _ _ measurable, semiproduct_apply _ _ _ measurable]
  apply lintegral_congr_ae
  exact equal.mono (fun input same => congrArg
    (fun current => current (Set.preimage (fun value => (input, value)) set)) same)

/-- Reverse semiproducts of s-finite kernels that agree almost everywhere under
the base measure are equal. -/
public theorem reverseSemiproduct_congr_ae (measure : Measure target)
    {left right : Kernel target source}
    (leftFinite : Kernel.IsSFinite left) (rightFinite : Kernel.IsSFinite right)
    (equal : measure.AEEq (fun input => left input) (fun input => right input)) :
    reverseSemiproduct measure left leftFinite = reverseSemiproduct measure right rightFinite := by
  unfold reverseSemiproduct
  rw [semiproduct_congr_ae measure leftFinite rightFinite equal]

end Problib.Measure.Measure
