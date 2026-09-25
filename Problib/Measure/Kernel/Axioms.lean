import Problib.Measure.Kernel
import Problib.Measure.Kernel.Basic.Axioms
import Problib.Measure.Kernel.Precomp.Axioms
import Problib.Measure.Kernel.Sum.Axioms
import Problib.Measure.Kernel.TotalVariation.Axioms
import Problib.Measure.Kernel.Comap.Axioms
import Problib.Measure.Kernel.Piecewise.Axioms
import Problib.Measure.Kernel.Finite.Axioms
import Problib.Measure.Kernel.Composition.Axioms
import Problib.Measure.Kernel.Density.Axioms
import Problib.Measure.Kernel.Measurable.Axioms
import Problib.Measure.Kernel.Product.Axioms
import Problib.Measure.Kernel.Randomization.Axioms
import Problib.Measure.Kernel.RadonNikodym.Axioms
import Problib.Measure.Kernel.Hahn.Axioms
import Problib.Measure.Kernel.Iteration.Axioms
import Problib.Measure.Kernel.Rejection.Axioms
import Problib.Measure.Kernel.Presentation.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.smul,
  Problib.Measure.Kernel.smul_apply,
  Problib.Measure.Kernel.IsFinite.smul,
  Problib.Measure.Kernel.FiniteReference.fiber,
  Problib.Measure.Kernel.FiniteReference.ofSFinite,
  Problib.Measure.Kernel.probabilityRepair,
  Problib.Measure.Kernel.probabilityRepair_eq,
  Problib.Measure.Kernel.probabilityRepair_isProbability,
  Problib.Measure.Kernel.probabilityRepair_isFinite,
  Problib.Measure.Kernel.probabilityRepair_aeEq,
  Problib.Measure.Kernel.ofDistributionBounds,
  Problib.Measure.Kernel.ofDistributionBounds_isProbability,
  Problib.Measure.Kernel.ofDistributionBounds_isFinite,
  Problib.Measure.Kernel.ofDistributionBounds_initial,
  Problib.Measure.Kernel.ofDistributionBounds_initial_le,
  Problib.Measure.Kernel.ofDistributionBounds_eq,
  Problib.Measure.Kernel.ofGenerator,
  Problib.Measure.Kernel.ofGenerator_apply,
  Problib.Measure.Kernel.ofDistributionFunction,
  Problib.Measure.Kernel.ofDistributionFunction_apply,
  Problib.Measure.Kernel.ofDistributionFunction_isProbability,
  Problib.Measure.Kernel.ofDistributionFunction_initial,
  Problib.Measure.Kernel.ofDistributionFunction_isFinite,
  Problib.Measure.Kernel.ofDistributionFunction_unique,
  Problib.Measure.Kernel.iSupIncreasing,
  Problib.Measure.Kernel.iSupIncreasing_apply,
  Problib.Measure.Kernel.iSupIncreasing_apply_measurable,
  Problib.Measure.Kernel.le_iSupIncreasing,
  Problib.Measure.Kernel.iSupIncreasing_le,
  Problib.Measure.Kernel.chain_le,
  Problib.Measure.Kernel.map_le,
  Problib.Measure.Kernel.map_iSupIncreasing,
  Problib.Measure.Kernel.add_iSupIncreasing,
  Problib.Measure.Kernel.comp_iSupIncreasing_right,
  Problib.Measure.Kernel.comp_iSupIncreasing_left,
  Problib.Measure.Kernel.comp_iSupIncreasing_diagonal,
  Problib.Measure.Kernel.IsFinite.iSupIncreasing_of_bound,
  Problib.Measure.Kernel.prefixSum,
  Problib.Measure.Kernel.prefixSum_congr,
  Problib.Measure.Kernel.map_prefixSum,
  Problib.Measure.Kernel.prefixSum_apply_measurable,
  Problib.Measure.Kernel.prefixSum_monotone,
  Problib.Measure.Kernel.IsSFinite.prefixSumFinite,
  Problib.Measure.Kernel.diagonalPrefixIncrement,
  Problib.Measure.Kernel.comp_prefixSum_eq_prefixSum_diagonalPrefixIncrement,
  Problib.Measure.Kernel.IsSFinite.diagonalPrefixIncrement,
  Problib.Measure.Kernel.sum_eq_iSupIncreasing_prefixSum,
  Problib.Measure.Kernel.IsSFinite.ofPrefixSum,
  Problib.Measure.Kernel.IsSFinite.compIncreasingOfPrefixSum
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
