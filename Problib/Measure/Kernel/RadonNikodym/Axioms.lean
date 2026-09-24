import Problib.Measure.Kernel.RadonNikodym
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.RadonNikodymDerivative.ofFiniteFibers,
  Problib.Measure.Kernel.RadonNikodymDerivative.sum,
  Problib.Measure.Kernel.RadonNikodymDerivative.ofSFiniteFiniteReference,
  Problib.Measure.Kernel.RadonNikodymDerivative.ofCommonFiniteReference,
  Problib.Measure.Kernel.RadonNikodymDerivative.ofCountableGenerator,
  Problib.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_of_countableGenerator,
  Problib.Measure.Kernel.RadonNikodymDerivative.ofStandardBorel,
  Problib.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_of_standardBorel,
  Problib.Measure.Kernel.RadonNikodymDerivative.fiber,
  Problib.Measure.Kernel.RadonNikodymDerivative.reconstruct_eq,
  Problib.Measure.Kernel.RadonNikodymDerivative.absolutelyContinuous,
  Problib.Measure.Kernel.RadonNikodymDerivative.lintegral_eq,
  Problib.Measure.Kernel.RadonNikodymDerivative.density_aeEq,
  Problib.Measure.Kernel.RadonNikodymDerivative.const,
  Problib.Measure.Kernel.RadonNikodymDerivative.identity,
  Problib.Measure.Kernel.RadonNikodymDerivative.trans,
  Problib.Measure.Kernel.RadonNikodymDerivative.zeroInfinityAbsolutelyContinuous,
  Problib.Measure.Kernel.RadonNikodymDerivative.density_aeInfinityEq,
  Problib.Measure.Kernel.RadonNikodymDerivative.ofCountableSource,
  Problib.Measure.Kernel.RadonNikodymDerivative.nonempty_iff_of_countable_source
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.RadonNikodym] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
