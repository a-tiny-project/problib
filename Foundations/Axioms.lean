import Foundations
import Foundations.Algebra.Axioms
import Foundations.Measure.Axioms
import Foundations.Probability.Finite.Interpretation.Axioms
import Foundations.QuasiBorel.Axioms
import Foundations.Real.Axioms
import Trust.Command

#audit_registered_claims

#audit_package [Foundations] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
