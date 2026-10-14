module

public import Problib.Analysis.PAP.Almost
public import Problib.Measure.Real.Pi

/-! Lebesgue measure on the finite Euclidean carriers integrates out its first
coordinate, so the null-zero-set and almost-everywhere derivative theorems hold
for it. -/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries
open Problib.Measure

noncomputable section

/-- Product Lebesgue measure integrates out its first coordinate. -/
public theorem volumePi_first_coordinate_tonelli :
    FirstCoordinateTonelli Problib.Measure.Real.volumePi := by
  intro dimension region measurable
  have mapped := Measure.map_apply
    (Measure.prod Problib.Measure.Real.volume
      (Problib.Measure.Real.volumePi dimension)
      (Problib.Measure.Real.volumePiSFinite dimension))
    (Problib.Measure.Real.finCons dimension)
    (Problib.Measure.Real.finCons_measurable dimension) measurable
  have product := Measure.prod_apply Problib.Measure.Real.volume
    (Problib.Measure.Real.volumePi dimension)
    (Problib.Measure.Real.volumePiSFinite dimension)
    (Problib.Measure.Real.finCons_measurable dimension measurable)
  rw [Problib.Measure.Real.volumePi_succ]
  exact mapped.trans product

/-- Nonvanishing analytic zero sets are Lebesgue null. -/
public theorem volumePi_null_analytic_zeros (dimension : Nat) :
    NullAnalyticZeros (Problib.Measure.Real.volumePi dimension) :=
  null_analytic_zeros_of_tonelli volumePi_first_coordinate_tonelli dimension

/-- Lebesgue-almost everywhere on its domain, a partial PAP map has the
intensional derivative as its coordinate derivatives. -/
public theorem PartialPAP.intensionalDerivative_ae_volumePi {source target : Nat}
    (map : PartialPAP source target) :
    (Problib.Measure.Real.volumePi source).AE (fun point => map.domain point →
      (∃ radius, lt zero radius ∧
        ∀ other, ball point radius other → map.domain other) ∧
      ∀ input output, HasDerivative
        (coordinateSliceAt (fun other => map.totalize other output) point input)
        zero (map.intensionalDerivative point input output)) :=
  map.intensionalDerivative_ae (volumePi_null_analytic_zeros source)

end

end Problib.Analysis.PAP
