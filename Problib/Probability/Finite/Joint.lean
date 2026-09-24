import Problib.Probability.Finite.Product

namespace Problib.Probability

universe u v

namespace FiniteMeasure

/-- A dependent pair measure: sample the outer value, then its indexed inner law. -/
def joint {Outer : Type u} {Inner : Type v}
    (outer : FiniteMeasure Outer) (inner : Outer → FiniteMeasure Inner) :
    FiniteMeasure (Outer × Inner) :=
  outer.bind fun outerValue =>
    (inner outerValue).map fun innerValue => (outerValue, innerValue)

private theorem mass_joint_kernel {Outer : Type u} {Inner : Type v}
    [DecidableEq Outer] [DecidableEq Inner]
    (inner : Outer → FiniteMeasure Inner)
    (outerPoint : Outer) (innerPoint : Inner) (outerValue : Outer) :
    ((inner outerValue).map fun innerValue => (outerValue, innerValue)).mass
        (outerPoint, innerPoint) =
      if outerValue = outerPoint then (inner outerPoint).mass innerPoint else 0 := by
  by_cases equal : outerValue = outerPoint
  · subst outerValue
    rw [if_pos rfl]
    apply mass_map_injective
    intro first second pairEqual
    exact congrArg Prod.snd pairEqual
  · rw [if_neg equal]
    apply mass_map_no_preimage
    intro innerValue pairEqual
    exact equal (congrArg Prod.fst pairEqual)

theorem mass_joint {Outer : Type u} {Inner : Type v}
    [DecidableEq Outer] [DecidableEq Inner]
    (outer : FiniteMeasure Outer) (inner : Outer → FiniteMeasure Inner)
    (outerPoint : Outer) (innerPoint : Inner) :
    (joint outer inner).mass (outerPoint, innerPoint) =
      outer.mass outerPoint * (inner outerPoint).mass innerPoint := by
  rw [joint, mass_bind]
  calc
    outer.integral (fun outerValue =>
        ((inner outerValue).map fun innerValue => (outerValue, innerValue)).mass
          (outerPoint, innerPoint)) =
        outer.integral (fun outerValue =>
          (if outerValue = outerPoint then 1 else 0) *
            (inner outerPoint).mass innerPoint) := by
              apply integral_congr
              intro outerValue
              rw [mass_joint_kernel]
              by_cases equal : outerValue = outerPoint
              · simp [equal]
              · simp [equal]
    _ = outer.integral (fun outerValue =>
          if outerValue = outerPoint then 1 else 0) *
        (inner outerPoint).mass innerPoint :=
      integral_mul_right outer
        (fun outerValue => if outerValue = outerPoint then 1 else 0)
        ((inner outerPoint).mass innerPoint)
    _ = outer.mass outerPoint * (inner outerPoint).mass innerPoint := by
      rw [← mass_eq_integral_indicator]

theorem joint_isDensity {Outer : Type u} {Inner : Type v}
    [DecidableEq Outer] [DecidableEq Inner]
    {outer outerReference : FiniteMeasure Outer}
    {inner innerReference : Outer → FiniteMeasure Inner}
    {outerDensity : Outer → NNRat} {innerDensity : Outer → Inner → NNRat}
    (outerCorrect : IsDensity outer outerReference outerDensity)
    (innerCorrect : ∀ outerValue,
      IsDensity (inner outerValue) (innerReference outerValue)
        (innerDensity outerValue)) :
    IsDensity (joint outer inner) (joint outerReference innerReference)
      (fun point => outerDensity point.1 * innerDensity point.1 point.2) := by
  intro point
  rw [mass_joint, mass_joint, outerCorrect point.1, innerCorrect point.1 point.2]
  exact NNRat.mul_mul_mul_comm _ _ _ _

end FiniteMeasure

end Problib.Probability
