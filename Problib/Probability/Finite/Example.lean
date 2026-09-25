import Problib.Probability.Finite.Density
import Problib.Probability.Finite.Distribution
import Problib.Probability.Finite.Expectation

namespace Problib.Probability.FiniteExample

def two : NNRat :=
  NNRat.ofRat 2 Rat.natCast_nonneg

theorem two_ne_zero : two ≠ 0 := by
  intro equal
  have values := congrArg NNRat.val equal
  change (2 : Rat) = 0 at values
  have naturals : (2 : Nat) = 0 := Rat.natCast_eq_zero_iff.mp values
  cases naturals

def half : NNRat :=
  NNRat.inverse two two_ne_zero

theorem two_eq_one_add_one : two = 1 + 1 := by
  apply NNRat.ext
  change (2 : Rat) = (1 : Rat) + (1 : Rat)
  exact Rat.natCast_add 1 1

theorem half_mul_two : half * two = 1 := by
  simpa [half] using NNRat.inverse_mul_self two two_ne_zero

theorem half_rat_mul_two : (half : Rat) * 2 = 1 := by
  have equality := congrArg NNRat.val half_mul_two
  simpa [two, NNRat.ofRat] using equality

theorem half_add_half : half + half = 1 := by
  calc
    half + half = half * (1 + 1) := by
      rw [NNRat.mul_add, NNRat.mul_one]
    _ = half * two := by rw [two_eq_one_add_one]
    _ = 1 := half_mul_two

theorem half_ne_zero : half ≠ 0 := by
  intro zero
  have impossible : (0 : NNRat) = 1 := by
    simpa [zero] using half_mul_two
  exact (by decide : (0 : NNRat) ≠ 1) impossible

theorem half_ne_one : half ≠ 1 := by
  intro equal
  have impossible := half_mul_two
  rw [equal] at impossible
  have twoEqual : (two : NNRat) = 1 :=
    (NNRat.one_mul two).symm.trans impossible
  have valuesEqual := congrArg NNRat.val twoEqual
  change (2 : Rat) = 1 at valuesEqual
  exact (by decide : (2 : Rat) ≠ 1) valuesEqual

theorem half_rat_ne_zero : (half : Rat) ≠ 0 := by
  intro zero
  have impossible : (0 : Rat) = 1 := by
    simpa [zero] using half_rat_mul_two
  exact (by decide : (0 : Rat) ≠ 1) impossible

theorem half_rat_ne_one : (half : Rat) ≠ 1 := by
  intro equal
  have impossible := half_rat_mul_two
  rw [equal] at impossible
  have twoEqual : (2 : Rat) = 1 :=
    (Rat.one_mul 2).symm.trans impossible
  exact (by decide : (2 : Rat) ≠ 1) twoEqual

def quarter : NNRat :=
  half * half

theorem quarter_ne_zero : quarter ≠ 0 :=
  NNRat.mul_ne_zero half_ne_zero half_ne_zero

theorem half_ne_quarter : half ≠ quarter := by
  intro equal
  have factorsEqual : half * 1 = half * half := calc
    half * 1 = half := NNRat.mul_one _
    _ = quarter := equal
    _ = half * half := rfl
  have oneEqualHalf := NNRat.mul_left_cancel half_ne_zero factorsEqual
  exact half_ne_one oneEqualHalf.symm

theorem quarter_ne_one : quarter ≠ 1 := by
  intro equal
  have halfEqualTwo : half = two := by
    have cancel : half * half = half * two := by
      rw [half_mul_two]
      exact equal
    exact NNRat.mul_left_cancel half_ne_zero cancel
  have sum := half_add_half
  rw [halfEqualTwo] at sum
  have valuesEqual := congrArg NNRat.val sum
  change ((2 : Nat) : Rat) + ((2 : Nat) : Rat) = 1 at valuesEqual
  rw [← Rat.natCast_add 2 2] at valuesEqual
  exact (by decide : ((4 : Nat) : Rat) ≠ 1) valuesEqual

def threeQuarters : NNRat :=
  quarter + half

theorem quarter_add_quarter : quarter + quarter = half := by
  calc
    quarter + quarter = half * (half + half) := (NNRat.mul_add half half half).symm
    _ = half * 1 := by rw [half_add_half]
    _ = half := NNRat.mul_one half

theorem quarter_add_threeQuarters : quarter + threeQuarters = 1 := by
  rw [threeQuarters, ← NNRat.add_assoc, quarter_add_quarter, half_add_half]

theorem threeQuarters_ne_zero : threeQuarters ≠ 0 := by
  intro zero
  have sum := quarter_add_threeQuarters
  rw [zero, NNRat.add_zero] at sum
  exact quarter_ne_one sum

def fairCoin : FinitePMF Bool where
  measure :=
    FiniteMeasure.scale half (FiniteMeasure.dirac false) +
      FiniteMeasure.scale half (FiniteMeasure.dirac true)
  total_one := by
    rw [FiniteMeasure.total_add, FiniteMeasure.total_scale, FiniteMeasure.total_scale,
      FiniteMeasure.total_dirac, FiniteMeasure.total_dirac]
    simpa using half_add_half

theorem fairCoin_expectation (observable : Bool → Rat) :
    fairCoin.expectation observable =
      (half : Rat) * observable false + (half : Rat) * observable true := by
  change (FiniteMeasure.mk [(false, half * 1), (true, half * 1)]).expectation
    observable = _
  simp [Rat.add_zero]

def headsLikelihood : Bool → NNRat
  | false => 0
  | true => two

theorem fairCoin_mass_false : fairCoin.prob false = half := by
  simp [fairCoin, FinitePMF.prob, FiniteMeasure.mass_add, FiniteMeasure.mass_scale,
    FiniteMeasure.mass_dirac]

theorem fairCoin_mass_true : fairCoin.prob true = half := by
  simp [fairCoin, FinitePMF.prob, FiniteMeasure.mass_add, FiniteMeasure.mass_scale,
    FiniteMeasure.mass_dirac, NNRat.add_comm]

def quarterCoin : FinitePMF Bool where
  measure :=
    FiniteMeasure.scale threeQuarters (FiniteMeasure.dirac false) +
      FiniteMeasure.scale quarter (FiniteMeasure.dirac true)
  total_one := by
    rw [FiniteMeasure.total_add, FiniteMeasure.total_scale, FiniteMeasure.total_scale,
      FiniteMeasure.total_dirac, FiniteMeasure.total_dirac, NNRat.mul_one, NNRat.mul_one,
      NNRat.add_comm]
    exact quarter_add_threeQuarters

theorem quarterCoin_mass_false : quarterCoin.prob false = threeQuarters := by
  simp [quarterCoin, FinitePMF.prob, FiniteMeasure.mass_add, FiniteMeasure.mass_scale,
    FiniteMeasure.mass_dirac]

theorem quarterCoin_mass_true : quarterCoin.prob true = quarter := by
  simp [quarterCoin, FinitePMF.prob, FiniteMeasure.mass_add, FiniteMeasure.mass_scale,
    FiniteMeasure.mass_dirac, NNRat.add_comm]

def certainTrue : FinitePMF Bool where
  measure := FiniteMeasure.dirac true
  total_one := FiniteMeasure.total_dirac true

theorem certainTrue_mass_false : certainTrue.prob false = 0 := by
  simp [certainTrue, FinitePMF.prob]

theorem certainTrue_mass_true : certainTrue.prob true = 1 := by
  simp [certainTrue, FinitePMF.prob]

theorem scored_coin_total : (fairCoin.score headsLikelihood).total = 1 := by
  rw [FinitePMF.score_total]
  calc
    fairCoin.measure.integral headsLikelihood =
        half * headsLikelihood false + half * headsLikelihood true := by
          simp [fairCoin, FiniteMeasure.integral_add, FiniteMeasure.integral_scale,
            FiniteMeasure.integral_dirac]
    _ = 1 := by simp [headsLikelihood, half_mul_two]

theorem scored_coin_false_mass : (fairCoin.score headsLikelihood).mass false = 0 := by
  rw [FinitePMF.score_mass, fairCoin_mass_false]
  simp [headsLikelihood]

theorem scored_coin_true_mass : (fairCoin.score headsLikelihood).mass true = 1 := by
  rw [FinitePMF.score_mass, fairCoin_mass_true]
  exact half_mul_two

theorem fairCoin_densitySimulation :
    FinitePMF.IsDensitySimulation fairCoin (fun _ => half)
      (FinitePMF.densitySimulation fairCoin fun _ => half) :=
  FinitePMF.densitySimulation_correct fairCoin fun _ => half

theorem fairCoin_support_density :
    FiniteMeasure.IsDensity fairCoin.measure
      (FiniteMeasure.supportCounting fairCoin.measure) fairCoin.measure.mass :=
  FiniteMeasure.support_isDensity fairCoin.measure

def fairCoinDistribution : FiniteDistribution Bool :=
  FiniteDistribution.ofPMF fairCoin

def encodePair (left right : Bool) : Nat :=
  if left then if right then 3 else 2 else if right then 1 else 0

theorem fair_coin_bind_order_commutes :
    (FiniteDistribution.bind fairCoinDistribution fun left =>
      FiniteDistribution.bind fairCoinDistribution fun right =>
        FiniteDistribution.pure (encodePair left right)) =
    (FiniteDistribution.bind fairCoinDistribution fun right =>
      FiniteDistribution.bind fairCoinDistribution fun left =>
        FiniteDistribution.pure (encodePair left right)) :=
  FiniteDistribution.bind_commute fairCoinDistribution fairCoinDistribution fun left right =>
    FiniteDistribution.pure (encodePair left right)

end Problib.Probability.FiniteExample
