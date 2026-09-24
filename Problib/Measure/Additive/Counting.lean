module

public import Problib.Measure.Additive.SFinite

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

/-- The counting measure on the discrete natural numbers. -/
public noncomputable def counting : Measure (Space.discrete Nat) :=
  Measure.sum (fun index => Measure.dirac (Space.discrete Nat) index)

/-- Singletons have measure one under the counting measure. -/
public theorem counting_singleton (point : Nat) :
    counting (fun value => value = point) = ENNReal.one := by
  rw [counting, Measure.sum_apply _ True.intro]
  rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ point]
  · exact Measure.dirac_apply_of_mem _ _ True.intro rfl
  · intro index different
    exact Measure.dirac_apply_of_not_mem _ _ True.intro different

/-- Full discrete natural space has infinite mass under counting measure. -/
public theorem counting_univ : counting Set.univ = ENNReal.top := by
  rw [counting, Measure.sum_apply _ (Space.discrete Nat).univ]
  calc
    ENNReal.tsum (fun index =>
        Measure.dirac (Space.discrete Nat) index Set.univ) =
        ENNReal.tsum (fun _ => ENNReal.one) :=
      ENNReal.tsum_congr (fun index => Measure.dirac_apply_univ _ index)
    _ = ENNReal.top := ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero

/-- The counting measure on the discrete natural numbers is sigma-finite. -/
public noncomputable def counting_sigmaFinite : SigmaFinite counting :=
  SigmaFinite.ofCover {
    sets := fun point value => value = point
    measurable := fun _ => True.intro
    finite := by
      intro point
      rw [counting_singleton]
      exact True.intro
    cover := by
      apply Set.ext
      intro value
      exact ⟨fun _ => True.intro, fun _ => ⟨value, rfl⟩⟩
  }

end Problib.Measure.Measure
