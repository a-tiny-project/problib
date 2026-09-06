import Foundations.Measure.Kernel
import Foundations.Measure.Kernel.Basic.Axioms
import Foundations.Measure.Kernel.Comap.Axioms
import Foundations.Measure.Kernel.Piecewise.Axioms
import Foundations.Measure.Kernel.Finite.Axioms
import Foundations.Measure.Kernel.Composition.Axioms
import Foundations.Measure.Kernel.Density.Axioms
import Foundations.Measure.Kernel.Measurable.Axioms
import Foundations.Measure.Kernel.Product.Axioms
import Foundations.Measure.Kernel.Randomization.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.probabilityRepair,
  Foundations.Measure.Kernel.probabilityRepair_eq,
  Foundations.Measure.Kernel.probabilityRepair_isProbability,
  Foundations.Measure.Kernel.probabilityRepair_isFinite,
  Foundations.Measure.Kernel.probabilityRepair_ae_eq,
  Foundations.Measure.Kernel.ofDistributionBounds,
  Foundations.Measure.Kernel.ofDistributionBounds_isProbability,
  Foundations.Measure.Kernel.ofDistributionBounds_isFinite,
  Foundations.Measure.Kernel.ofDistributionBounds_initial,
  Foundations.Measure.Kernel.ofDistributionBounds_initial_le,
  Foundations.Measure.Kernel.ofDistributionBounds_eq,
  Foundations.Measure.Kernel.ofGenerator,
  Foundations.Measure.Kernel.ofGenerator_apply,
  Foundations.Measure.Kernel.ofDistributionFunction,
  Foundations.Measure.Kernel.ofDistributionFunction_apply,
  Foundations.Measure.Kernel.ofDistributionFunction_isProbability,
  Foundations.Measure.Kernel.ofDistributionFunction_initial,
  Foundations.Measure.Kernel.ofDistributionFunction_isFinite,
  Foundations.Measure.Kernel.ofDistributionFunction_unique
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
