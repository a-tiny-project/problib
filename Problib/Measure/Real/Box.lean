module

public import Problib.Measure.Real.Pi
public import Problib.Analysis.Real.FiniteVector.Borel

/-! # Volume of centered boxes

The box `[-bound, bound]ⁿ` has finite product volume. A construction that needs
pieces of finite volume cuts its region by these boxes. The proof peels one coordinate per
dimension, in the order `volumePi_succ` prepends them.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector (closedBox closedBox_measurable)

public section

/-- The box `[-bound, bound]ⁿ`. -/
@[expose] public def centeredBox (dimension bound : Nat) : Set (Fin dimension → Carrier) :=
  closedBox (fun _ => neg (selection.ofRat (bound : Rat))) (fun _ => selection.ofRat (bound : Rat))

public theorem centeredBox_measurable (dimension bound : Nat) :
    (Space.pi (fun _ : Fin dimension => borel)).Measurable (centeredBox dimension bound) :=
  closedBox_measurable _ _

/-- Prepending a coordinate in `[-bound, bound]` to a point of the smaller box
lands in the larger box, and only such points do. -/
private theorem preimage_finCons_centeredBox (dimension bound : Nat) :
    Set.preimage (finCons dimension) (centeredBox (dimension + 1) bound) =
      Set.product (Icc (neg (selection.ofRat (bound : Rat))) (selection.ofRat (bound : Rat)))
        (centeredBox dimension bound) := by
  apply Set.ext
  intro pair
  constructor
  · intro inside
    exact ⟨inside 0, fun coordinate => inside coordinate.succ⟩
  · intro inside coordinate
    refine Fin.cases ?_ (fun earlier => ?_) coordinate
    · exact inside.1
    · exact inside.2 earlier

/-- Every centered box has finite product volume. -/
public theorem volumePi_centeredBox_finite :
    (dimension bound : Nat) → ENNReal.Finite (volumePi dimension (centeredBox dimension bound))
  | 0, bound => by
      rw [volumePi_zero]
      exact ENNReal.finite_of_le (Measure.mono _ (Set.subset_univ _))
        (by rw [Measure.dirac_apply_univ]; exact True.intro)
  | dimension + 1, bound => by
      rw [volumePi_succ, Measure.map_apply _ _ _ (centeredBox_measurable _ bound),
        preimage_finCons_centeredBox, Measure.prod_apply_product _ _ _
          (measurable_icc _ _) (centeredBox_measurable dimension bound), volume_icc]
      exact ENNReal.mul_finite (ENNReal.ofReal_finite _)
        (volumePi_centeredBox_finite dimension bound)

end

end Problib.Measure.Real
