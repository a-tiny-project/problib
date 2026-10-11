module

public import Problib.Analysis.Trigonometric.Analytic
public import Problib.Analysis.PAP.Measurable
import Problib.Real.Grind

/-! Sine and cosine are Borel measurable.

A lower ray's preimage under a function analytic on the line is the
sublevel set where the shifted function is nonpositive. That set is measurable
in the one-coordinate product space, and the line's embedding as the constant
vector carries it back to the real Borel space.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

noncomputable section

private theorem line_measurable :
    MeasurableMap borel (vectorBorel 1) (fun value : selection.Carrier => fun _ => value) :=
  Space.pi_measurable (fun _ _ measurable => measurable)

/-- A function analytic on the whole line is Borel measurable. -/
private theorem measurable_of_analytic {function : selection.Carrier → selection.Carrier}
    (analytic : AnalyticOn (fun _ : carrier 1 => True) (fun point => function (point 0))) :
    MeasurableMap borel borel function := by
  apply measurableMap_borel_iff_iic.mpr
  intro upper
  have shifted := analytic_on_add analytic
    (analytic_on_constant (is_open_univ 1) (neg upper))
  have sublevel := line_measurable
    (PAP.analytic_sublevel_measurable shifted)
  have equal : Set.preimage (fun value : selection.Carrier => fun _ : Fin 1 => value)
      (fun point : carrier 1 => True ∧ le (add (function (point 0)) (neg upper)) zero) =
      Set.preimage function (Iic upper) := by
    apply Set.ext
    intro value
    change (True ∧ le (add (function value) (neg upper)) zero) ↔ le (function value) upper
    constructor
    · intro below
      have bound := below.2
      real_grind
    · intro below
      exact ⟨True.intro, by real_grind⟩
  rw [← equal]
  exact sublevel

public theorem sin_measurable : MeasurableMap borel borel sin :=
  measurable_of_analytic analytic_on_sin

public theorem cos_measurable : MeasurableMap borel borel cos :=
  measurable_of_analytic analytic_on_cos

end

end Problib.Analysis
