import Problib.Probability.Finite.Estimator.Core
import Problib.Probability.Finite.Example

set_option autoImplicit false

namespace Problib.Probability.FiniteEstimator.Necessity

open Problib.Probability
open Problib.Probability.FiniteExample
open Problib.Probability.FiniteEstimator

def indicator : Bool → Rat
  | false => 0
  | true => 1

theorem indicator_unbiased :
    Unbiased fairCoin indicator (half : Rat) := by
  constructor
  rw [fairCoin_expectation]
  change (half : Rat) * 0 + (half : Rat) * 1 = (half : Rat)
  rw [Rat.mul_zero, Rat.mul_one, Rat.zero_add]

theorem correlated_product_mean :
    fairCoin.expectation (multiplyEstimate indicator indicator) = (half : Rat) := by
  rw [fairCoin_expectation]
  change (half : Rat) * (0 * 0) + (half : Rat) * (1 * 1) = (half : Rat)
  rw [Rat.zero_mul, Rat.mul_zero, Rat.one_mul, Rat.mul_one, Rat.zero_add]

theorem correlated_product_is_biased :
    ¬Unbiased fairCoin (multiplyEstimate indicator indicator)
      ((half : Rat) * (half : Rat)) := by
  intro claimed
  have mean := claimed.mean
  rw [correlated_product_mean] at mean
  have unequal : (half : Rat) ≠ (quarter : Rat) := by
    intro equal
    exact half_ne_quarter (NNRat.ext equal)
  apply unequal
  exact mean.trans (by rfl)

theorem independence_premise_is_necessary :
    ¬MomentFactorizes fairCoin indicator indicator := by
  intro factorized
  exact correlated_product_is_biased
    (multiply_unbiased_of_factorized_moment indicator_unbiased indicator_unbiased factorized)

def badCoupling : FinitePMF (Bool × Bool) :=
  FinitePMF.map (fun value => (false, value)) fairCoin

theorem badCoupling_does_not_have_the_claimed_left_marginal :
    ¬Couples badCoupling fairCoin fairCoin := by
  intro claimed
  have marginal := claimed.left_marginal indicator
  have leftZero : badCoupling.expectation (fun pair => indicator pair.1) = 0 := by
    rw [badCoupling, FinitePMF.expectation_map, fairCoin_expectation]
    change (half : Rat) * 0 + (half : Rat) * 0 = 0
    rw [Rat.mul_zero, Rat.zero_add]
  rw [leftZero] at marginal
  have rightHalf : fairCoin.expectation indicator = (half : Rat) := indicator_unbiased.mean
  rw [rightHalf] at marginal
  exact half_rat_ne_zero marginal.symm

end Problib.Probability.FiniteEstimator.Necessity
