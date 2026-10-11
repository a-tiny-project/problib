module

public import Problib.Analysis.Gaussian.Network.Block
import Problib.Real.Grind

/-! A vector observation with independent Gaussian noise, one coordinate at a time.

An observation `y ~ N(e + H x, diag r)` of a network's nodes `x` is a list of
scalar observations, one row each: `yⱼ ~ N(eⱼ + ⟨Hⱼ, x⟩, rⱼ)`. Its likelihood is
the product of the scalar Gaussian densities (`likelihood`). Weighting the
network's law by it applies L6a's `score_collapse` once per coordinate, in
order, each to the network the last one left (`Network.observe`). The evidence
is the product of the scalar evidences, positive and finite
(`observe_positive_finite`), and the result keeps the network's length
(`length_observe`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- Observation rows that read every node of a network of `count` nodes, with
positive noise. -/
@[expose] public def ObservesAll (count : Nat) (rows : List Row) : Prop :=
  ∀ row ∈ rows, row.coefficients.length = count ∧ lt zero row.variance

/-- The likelihood `Πⱼ N(yⱼ; eⱼ + ⟨Hⱼ, x⟩, rⱼ)` of the observed values at the
nodes `x`, over the shorter of the rows and the values. -/
@[expose] public def likelihood : List Row → List Carrier → List Carrier → ENNReal
  | row :: rows, values, observed :: rest =>
      ENNReal.mul (ENNReal.finite (Gaussian.density (row.mean values) row.variance observed))
        (likelihood rows values rest)
  | _, _, _ => ENNReal.one

public theorem likelihood_measurable (rows : List Row) (observed : List Carrier) :
    ENNRealMeasurable (Space.list borel) (fun values => likelihood rows values observed) := by
  induction rows generalizing observed with
  | nil => exact ENNRealMeasurable.constant _ _
  | cons row rows induction =>
      cases observed with
      | nil => exact ENNRealMeasurable.constant _ _
      | cons value rest =>
          have pairing : MeasurableMap (Space.list borel) (Space.product (Space.list borel) borel)
              (fun values => (values, value)) :=
            Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ borel value)
          have composed := ENNRealMeasurable.comp row.pairDensity_measurable pairing
          exact ENNRealMeasurable.mul composed (induction rest)

/-- The scalar observation a row makes of a network it reads in full. -/
@[expose] public def Row.observation (row : Row) (network : Network)
    (reads : row.coefficients.length = network.length) (positive : lt zero row.variance) :
    Observation network where
  intercept := row.intercept
  coefficients := row.coefficients
  shaped := reads
  variance := row.variance
  positive := positive

/-- Positive and finite. -/
@[expose] public def PositiveFinite (value : ENNReal) : Prop :=
  ENNReal.lt ENNReal.zero value ∧ value ≠ ENNReal.top

public theorem PositiveFinite.one : PositiveFinite ENNReal.one :=
  ⟨ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero, ENNReal.finite_ne_top _⟩

public theorem PositiveFinite.mul {left right : ENNReal} (leftHolds : PositiveFinite left)
    (rightHolds : PositiveFinite right) : PositiveFinite (ENNReal.mul left right) :=
  ⟨ENNReal.zero_lt_iff_ne_zero.mpr fun vanished =>
      (ENNReal.mul_eq_zero_iff.mp vanished).elim (ENNReal.zero_lt_iff_ne_zero.mp leftHolds.1)
        (ENNReal.zero_lt_iff_ne_zero.mp rightHolds.1),
    ENNReal.finite_iff_ne_top.mp (ENNReal.mul_finite (ENNReal.finite_iff_ne_top.mpr leftHolds.2)
      (ENNReal.finite_iff_ne_top.mpr rightHolds.2))⟩

namespace Network

open Classical in
/-- Update by each scalar observation in turn, multiplying the evidences. A row
that does not read the network in full, or has no positive variance, stops
the update; `ObservesAll` rules both out. -/
@[expose] public def observe (network : Network) : List Row → List Carrier → Network × ENNReal
  | row :: rows, observed :: rest =>
      if valid : row.coefficients.length = network.length ∧ lt zero row.variance then
        let updated := network.update (row.observation network valid.1 valid.2) observed
        let next := updated.observe rows rest
        (next.1, ENNReal.mul ((row.observation network valid.1 valid.2).evidence observed) next.2)
      else (network, ENNReal.one)
  | _, _ => (network, ENNReal.one)

public theorem length_observe (network : Network) (rows : List Row) (observed : List Carrier) :
    (network.observe rows observed).1.length = network.length := by
  induction rows generalizing network observed with
  | nil => rfl
  | cons row rows induction =>
      cases observed with
      | nil => rfl
      | cons value rest =>
          unfold observe
          split
          · exact (induction _ rest).trans (network.length_update _ _)
          · rfl

public theorem observe_positive_finite (network : Network) (rows : List Row)
    (observed : List Carrier) : PositiveFinite (network.observe rows observed).2 := by
  induction rows generalizing network observed with
  | nil => exact PositiveFinite.one
  | cons row rows induction =>
      cases observed with
      | nil => exact PositiveFinite.one
      | cons value rest =>
          unfold observe
          split
          next valid =>
            exact PositiveFinite.mul
              ((row.observation network valid.1 valid.2).evidence_positive_finite value)
              (induction (network.update (row.observation network valid.1 valid.2) value) rest)
          next => exact PositiveFinite.one

/-- Weighting by a scalar multiple's density scales the weighted measure. -/
public theorem smul_withDensity_left (law : Measure (Space.list borel)) (scalar : ENNReal)
    {density : List Carrier → ENNReal} (measurable : ENNRealMeasurable (Space.list borel) density) :
    (Measure.smul scalar law).withDensity density =
      Measure.smul scalar (law.withDensity density) := by
  rw [← Measure.withDensity_const,
    Measure.withDensity_withDensity _ (ENNRealMeasurable.constant _ _)
    measurable, Measure.smul_withDensity _ _ measurable]

/-- Weighting a network by a vector observation's likelihood is the product of
the scalar evidences times the law of the network updated by each coordinate
in turn. -/
public theorem observe_law (network : Network) (rows : List Row) (observed : List Carrier)
    (observes : ObservesAll network.length rows) (counted : observed.length = rows.length) :
    network.law.withDensity (fun values => likelihood rows values observed) =
      Measure.smul (network.observe rows observed).2 (network.observe rows observed).1.law := by
  induction rows generalizing network observed with
  | nil =>
      change network.law.withDensity (fun _ => ENNReal.one) = Measure.smul ENNReal.one network.law
      rw [Measure.withDensity_const]
  | cons row rows induction =>
      match observed, counted with
      | value :: rest, counted =>
          have valid := observes row (List.mem_cons_self ..)
          let scalar := row.observation network valid.1 valid.2
          have updatedObserves : ObservesAll (network.update scalar value).length rows := by
            rw [network.length_update]
            exact fun current member => observes current (List.mem_cons_of_mem _ member)
          have step : network.observe (row :: rows) (value :: rest) =
              (((network.update scalar value).observe rows rest).1,
                ENNReal.mul (scalar.evidence value)
                  ((network.update scalar value).observe rows rest).2) := by
            conv => lhs; rw [observe]
            rw [dite_eq_left_of_eq_true (eq_true valid)]
          rw [step]
          change network.law.withDensity (fun values =>
              ENNReal.mul (scalar.likelihood values value) (likelihood rows values rest)) = _
          rw [← Measure.withDensity_withDensity _ (scalar.likelihood_measurable value)
              (likelihood_measurable rows rest),
            network.score_collapse scalar value,
            smul_withDensity_left _ _ (likelihood_measurable rows rest),
            induction _ rest updatedObserves (by simpa using counted),
            Measure.smul_smul]

end Network

end
end Problib.Analysis.Gaussian
