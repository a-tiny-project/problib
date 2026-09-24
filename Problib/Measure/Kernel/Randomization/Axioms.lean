import Problib.Measure.Kernel.Randomization
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.Randomizer,
  Problib.Measure.Kernel.Randomizer.fiber_measurable,
  Problib.Measure.Kernel.Randomizer.isProbability,
  Problib.Measure.Kernel.Randomizer.map,
  Problib.Measure.Kernel.Randomizer.ofEmbedding,
  Problib.Measure.Kernel.Randomizer.Unit.bounds,
  Problib.Measure.Kernel.Randomizer.Unit.bounds_measurable,
  Problib.Measure.Kernel.Randomizer.Unit.distribution,
  Problib.Measure.Kernel.Randomizer.Unit.distribution_slices,
  Problib.Measure.Kernel.Randomizer.Unit.distribution_measure,
  Problib.Measure.Kernel.Randomizer.Unit.decoder,
  Problib.Measure.Kernel.Randomizer.Unit.decoder_measurable,
  Problib.Measure.Kernel.Randomizer.Unit.decoder_law,
  Problib.Measure.Kernel.Randomizer.ofUnitInterval,
  Problib.Measure.Kernel.Randomizer.ofStandardBorel,
  Problib.Measure.Kernel.Randomizer.nonempty_iff_probability
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Randomization] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
