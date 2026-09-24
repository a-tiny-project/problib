import Problib.Measure.Kernel.Hahn
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.Kernel.HahnDecomposition.fiber,
  Problib.Measure.Kernel.HahnDecomposition.complement,
  Problib.Measure.Kernel.Hahn.score_measurable,
  Problib.Measure.Kernel.Hahn.supremum_measurable,
  Problib.Measure.Kernel.Hahn.defect_measurable,
  Problib.Measure.Kernel.Hahn.exists_approximation,
  Problib.Measure.Kernel.exists_hahnDecomposition_of_countableGenerator,
  Problib.Measure.Kernel.HahnDecomposition.ofCountableGenerator
]

#audit_registered_claims

#audit_package [Problib.Measure.Kernel.Hahn] allowing [propext, Quot.sound, Classical.choice]
