import Foundations.Measure.Kernel.Randomization
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.Randomizer,
  Foundations.Measure.Kernel.Randomizer.fiber_measurable,
  Foundations.Measure.Kernel.Randomizer.isProbability,
  Foundations.Measure.Kernel.Randomizer.map,
  Foundations.Measure.Kernel.Randomizer.ofEmbedding,
  Foundations.Measure.Kernel.Randomizer.Unit.bounds,
  Foundations.Measure.Kernel.Randomizer.Unit.bounds_measurable,
  Foundations.Measure.Kernel.Randomizer.Unit.distribution,
  Foundations.Measure.Kernel.Randomizer.Unit.distribution_slices,
  Foundations.Measure.Kernel.Randomizer.Unit.distribution_measure,
  Foundations.Measure.Kernel.Randomizer.Unit.decoder,
  Foundations.Measure.Kernel.Randomizer.Unit.decoder_measurable,
  Foundations.Measure.Kernel.Randomizer.Unit.decoder_law,
  Foundations.Measure.Kernel.Randomizer.ofUnitInterval,
  Foundations.Measure.Kernel.Randomizer.ofStandardBorel,
  Foundations.Measure.Kernel.Randomizer.nonempty_iff_probability
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Randomization] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
