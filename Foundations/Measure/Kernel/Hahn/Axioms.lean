import Foundations.Measure.Kernel.Hahn
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Measure.Kernel.HahnDecomposition.fiber,
  Foundations.Measure.Kernel.HahnDecomposition.complement,
  Foundations.Measure.Kernel.Hahn.score_measurable,
  Foundations.Measure.Kernel.Hahn.supremum_measurable,
  Foundations.Measure.Kernel.Hahn.defect_measurable,
  Foundations.Measure.Kernel.Hahn.exists_approximation,
  Foundations.Measure.Kernel.exists_hahnDecomposition_ofCountableGenerator,
  Foundations.Measure.Kernel.HahnDecomposition.ofCountableGenerator
]

#audit_registered_claims

#audit_package [Foundations.Measure.Kernel.Hahn] allowing [propext, Quot.sound, Classical.choice]
