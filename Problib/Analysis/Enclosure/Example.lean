module

public import Problib.Analysis.Enclosure.Exp
public import Problib.Analysis.Enclosure.Log
public import Problib.Analysis.Enclosure.Sqrt
public import Problib.Analysis.Enclosure.Pi

/-! The enclosures at fixed witnesses, checked by the kernel.

Each witness runs an enclosure on rational endpoints by `decide +kernel` at
the default heartbeat limit, with no `native_decide`, and reads off a decimal
bracket from the containment theorem. The width bound is the issue's target
of one part in `10^12`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real
open Problib.Real.Construction
open Problib.Real.Construction.Dedekind

/-- One part in `10^12`. -/
@[expose] public def trillionth : Rat := 1 / 1000000000000

/-- The enclosure of `exp 1` at precision 44 is narrower than `10^-12`. -/
public theorem exp_one_width : ((Interval.point 1).exp 44).width ≤ trillionth := by
  decide +kernel

/-- The same exponential witness is strictly narrower than `10^-12`. -/
public theorem exp_one_strict_width : ((Interval.point 1).exp 44).width < trillionth := by
  decide +kernel

/-- `exp 1` lies in `[2.718281828459, 2.718281828460]`. -/
public theorem exp_one_bracket :
    le (selection.ofRat (2718281828459 / 1000000000000)) (Problib.Analysis.exp one) ∧
      le (Problib.Analysis.exp one) (selection.ofRat (2718281828460 / 1000000000000)) := by
  have member := (Interval.contains_point 1).exp 48
  rw [ofRat_one] at member
  have bracket : 2718281828459 / 1000000000000 ≤ ((Interval.point 1).exp 48).lo ∧
      ((Interval.point 1).exp 48).hi ≤ 2718281828460 / 1000000000000 := by
    decide +kernel
  exact ⟨le_trans ((ofRat_le_iff _ _).mpr bracket.1) member.1,
    le_trans member.2 ((ofRat_le_iff _ _).mpr bracket.2)⟩

/-- The enclosure of `log 2` at precision 42 exists and is narrower than
`10^-12`. -/
public theorem log_two_width :
    ((Interval.point 2).log? 42).any (fun result => decide (result.width < trillionth)) =
      true := by
  decide +kernel

/-- `log 2` lies in `[0.693147180559, 0.693147180560]`. -/
public theorem log_two_bracket :
    le (selection.ofRat (693147180559 / 1000000000000))
        (Logarithm.logIntegral (selection.ofRat 2)) ∧
      le (Logarithm.logIntegral (selection.ofRat 2))
        (selection.ofRat (693147180560 / 1000000000000)) :=
  (Interval.contains_point 2).log_bracket (precision := 48) (by decide +kernel)

/-- The enclosure of `√2` at precision 40 exists and is narrower than
`10^-12`. -/
public theorem sqrt_two_width :
    ((Interval.point 2).sqrt? 40).any (fun result => decide (result.width < trillionth)) =
      true := by
  decide +kernel

/-- `√2` lies in `[1.414213562373, 1.414213562374]`. -/
public theorem sqrt_two_bracket :
    le (selection.ofRat (1414213562373 / 1000000000000))
        (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat 2))).val ∧
      le (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat 2))).val
        (selection.ofRat (1414213562374 / 1000000000000)) :=
  (Interval.contains_point 2).sqrt_bracket (precision := 44) (by decide +kernel)

/-- Zero is included in the square root's domain. -/
public theorem sqrt_zero_enclosure :
    (Interval.point 0).sqrt? 4 = some ⟨0, 1 / 16, by decide +kernel⟩ := by
  with_unfolding_all rfl

/-- A negative point is refused by the square root's enclosure. -/
public theorem sqrt_negative_refused : (Interval.point (-1)).sqrt? 4 = none := rfl

/-- The enclosure of pi at precision 42 is narrower than `10^-12`. -/
public theorem pi_width : (Interval.pi 42).width < trillionth := by
  decide +kernel

/-- Pi lies in `[3.141592653589, 3.141592653590]`. -/
public theorem pi_bracket :
    le (selection.ofRat (3141592653589 / 1000000000000)) Problib.Analysis.pi ∧
      le Problib.Analysis.pi (selection.ofRat (3141592653590 / 1000000000000)) := by
  have member := Interval.contains_pi 48
  have bracket : 3141592653589 / 1000000000000 ≤ (Interval.pi 48).lo ∧
      (Interval.pi 48).hi ≤ 3141592653590 / 1000000000000 := by
    decide +kernel
  exact ⟨le_trans ((ofRat_le_iff _ _).mpr bracket.1) member.1,
    le_trans member.2 ((ofRat_le_iff _ _).mpr bracket.2)⟩

/-- The zero-precision pi enclosure is pinned by reduction. -/
public theorem pi_zero_precision : Interval.pi 0 = ⟨2, 4, by decide +kernel⟩ := by
  with_unfolding_all rfl

end Problib.Analysis.Enclosure
