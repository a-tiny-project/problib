import Foundations.Measure.Kernel.RadonNikodym
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofFiniteFibers,
  Foundations.Measure.Kernel.RadonNikodymDerivative.sum,
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofSFiniteFiniteReference,
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofCommonFiniteReference,
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofCountableGenerator,
  Foundations.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_ofCountableGenerator,
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofStandardBorel,
  Foundations.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_ofStandardBorel,
  Foundations.Measure.Kernel.RadonNikodymDerivative.fiber,
  Foundations.Measure.Kernel.RadonNikodymDerivative.reconstruct_eq,
  Foundations.Measure.Kernel.RadonNikodymDerivative.absolutelyContinuous,
  Foundations.Measure.Kernel.RadonNikodymDerivative.lintegral_eq,
  Foundations.Measure.Kernel.RadonNikodymDerivative.density_ae_eq,
  Foundations.Measure.Kernel.RadonNikodymDerivative.const,
  Foundations.Measure.Kernel.RadonNikodymDerivative.identity,
  Foundations.Measure.Kernel.RadonNikodymDerivative.trans,
  Foundations.Measure.Kernel.RadonNikodymDerivative.zeroInfinityAbsolutelyContinuous,
  Foundations.Measure.Kernel.RadonNikodymDerivative.density_aeInfinityEq,
  Foundations.Measure.Kernel.RadonNikodymDerivative.ofCountableSource,
  Foundations.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_ofCountableSource
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.RadonNikodym] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
