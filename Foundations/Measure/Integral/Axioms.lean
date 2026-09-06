import Foundations.Measure.Integral
import Foundations.Measure.Integral.Density.Axioms
import Foundations.Measure.Integral.Lebesgue.Axioms
import Foundations.Measure.Integral.Simple.Axioms
import Trust.Command

#audit_registered_claims

#audit_package [Foundations.Measure.Integral] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
