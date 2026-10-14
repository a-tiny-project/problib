import Problib
import Problib.Algebra.Axioms
import Problib.Analysis.Axioms
import Problib.Countable.Axioms
import Problib.Domain.Axioms
import Problib.Inference.Axioms
import Problib.Measure.Axioms
import Problib.Probability.Finite.Interpretation.Axioms
import Problib.QuasiBorel.Axioms
import Problib.Real.Axioms
import Trust.Command

#audit_registered_claims

#audit_package [Problib] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
