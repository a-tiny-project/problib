module

public import Problib.Analysis.Gaussian.Network.Collapse
import Problib.Real.Grind

set_option autoImplicit false

/-!
# Score collapse at one node

A Normal node `μ ~ N(m, v)` read once by `y ~ N(μ, w)` is the network
collapse of `Collapse.lean` at one row. Pointwise, the prior density times the
likelihood is the evidence `N(y; m, v + w)` times the posterior density of `μ`
(`scalar_collapse_density`). The posterior has the precision-weighted mean
`(m w + v y)/(v + w)` and the variance `v w/(v + w)`. Integrated, weighting the
prior law by the likelihood is the evidence times the posterior law
(`scalar_score_collapse`). Both follow from `Observation.collapse_density` at
the one-node network, whose update is computed row by row, with no other
Gaussian identity.
-/

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

public section

noncomputable section

/-- The network of one node, Normal at `mean` with variance `variance`. -/
@[expose] def Network.single (mean variance : Carrier) (positive : lt zero variance) : Network where
  rows := [⟨mean, [], variance⟩]
  triangular := fun index row found => by
    cases index with
    | zero =>
        cases Option.some.inj found
        rfl
    | succ => cases found
  positive := fun row member => by
    cases member with
    | head => exact positive
    | tail _ inside => cases inside

/-- The observation of a one-node network with coefficient one. -/
@[expose] def Network.reading (network : Network) (single : network.length = 1)
    (variance : Carrier) (positive : lt zero variance) : Observation network where
  intercept := zero
  coefficients := [one]
  shaped := single.symm
  variance := variance
  positive := positive

/-- The posterior mean of a Normal node `N(m, v)` after one reading `y` with
variance `w`. -/
@[expose] def scalarMean (mean variance readingVariance observed : Carrier) : Carrier :=
  div (add (mul mean readingVariance) (mul variance observed)) (add variance readingVariance)

/-- The posterior variance of a Normal node with variance `v` after one reading
with variance `w`. -/
@[expose] def scalarVariance (variance readingVariance : Carrier) : Carrier :=
  div (mul variance readingVariance) (add variance readingVariance)

theorem scalarVariance_positive {variance readingVariance : Carrier}
    (positive : lt zero variance) (readingPositive : lt zero readingVariance) :
    lt zero (scalarVariance variance readingVariance) :=
  div_positive (mul_positive positive readingPositive) (add_positive positive readingPositive)

/-- A one-node network's density at a list of one is its node's density. -/
theorem Network.single_density (mean variance : Carrier) (positive : lt zero variance)
    (value : Carrier) :
    (Network.single mean variance positive).density [value] = Gaussian.density mean variance value := by
  unfold Network.density
  change NNReal.mul (Gaussian.density (add mean zero) variance value) NNReal.one = _
  rw [NNReal.mul_one, show add mean zero = mean by real_grind]

/-- **Pointwise scalar collapse.** The prior density of `μ` times the
likelihood of `y` is the evidence at `y` times the posterior density of `μ`. -/
theorem scalar_collapse_density (mean variance readingVariance observed value : Carrier)
    (positive : lt zero variance) (readingPositive : lt zero readingVariance) :
    ENNReal.mul (ENNReal.finite (density mean variance value))
        (ENNReal.finite (density value readingVariance observed)) =
      ENNReal.mul (ENNReal.finite (density mean (add variance readingVariance) observed))
        (ENNReal.finite (density (scalarMean mean variance readingVariance observed)
          (scalarVariance variance readingVariance) value)) := by
  let network := Network.single mean variance positive
  let observation := network.reading rfl readingVariance readingPositive
  let gain := pairGain variance readingVariance one
  have updated : network.update observation observed =
      Network.single (add (sub mean (mul gain (add zero (mul one mean)))) (mul gain observed)) _
        (pairConditional_positive positive readingPositive one) :=
    Network.ext rfl
  have collapse := observation.collapse_density observed [value]
  rw [updated, Network.single_density, Network.single_density] at collapse
  have nonzero := nonzero_of_positive positive
  have readingNonzero := nonzero_of_positive readingPositive
  have sumNonzero := nonzero_of_positive (add_positive positive readingPositive)
  have reads : add zero (add (mul one value) zero) = value := by real_grind
  have meanOne : add zero (mul one mean) = mean := by real_grind
  have pair : pairVariance variance readingVariance one = add variance readingVariance := by
    unfold pairVariance
    real_grind
  have posteriorMean : add (sub mean (mul gain mean)) (mul gain observed) =
      scalarMean mean variance readingVariance observed := by
    simp only [gain, pairGain, pair, scalarMean]
    real_grind
  change ENNReal.mul _ (ENNReal.finite (density (add zero (add (mul one value) zero))
      readingVariance observed)) =
    ENNReal.mul (ENNReal.finite (density (add zero (mul one mean))
      (pairVariance variance readingVariance one) observed))
      (ENNReal.finite (density _ (div (mul variance readingVariance)
        (pairVariance variance readingVariance one)) value)) at collapse
  rw [reads, meanOne, pair, posteriorMean] at collapse
  exact collapse

/-- **Scalar score collapse.** Weighting the prior law `N(m, v)` by the
likelihood of `y` is the evidence at `y` times the posterior law. -/
theorem scalar_score_collapse (mean variance readingVariance observed : Carrier)
    (positive : lt zero variance) (readingPositive : lt zero readingVariance) :
    (law mean variance).withDensity
        (fun value => ENNReal.finite (density value readingVariance observed)) =
      Measure.smul (ENNReal.finite (density mean (add variance readingVariance) observed))
        (law (scalarMean mean variance readingVariance observed)
          (scalarVariance variance readingVariance)) := by
  have likelihoodMeasurable : ENNRealMeasurable borel
      fun value => ENNReal.finite (density value readingVariance observed) :=
    ENNRealMeasurable.comp
      (map := fun p : (Carrier × Carrier) × Carrier => ENNReal.finite (density p.1.1 p.1.2 p.2))
      (before := fun value : Carrier => ((value, readingVariance), observed))
      density_measurable
      (Space.pair_measurable
        (Space.pair_measurable (MeasurableMap.identity borel)
          (MeasurableMap.constant borel borel readingVariance))
        (MeasurableMap.constant borel borel observed))
  rw [law_eq_withDensity _ _ positive,
    law_eq_withDensity _ _ (scalarVariance_positive positive readingPositive),
    Measure.withDensity_withDensity _ (density_measurable_slice _ _) likelihoodMeasurable,
    Measure.smul_withDensity _ _ (density_measurable_slice _ _)]
  exact congrArg _ (funext fun value =>
    scalar_collapse_density mean variance readingVariance observed value positive readingPositive)

end

end

end Problib.Analysis.Gaussian
