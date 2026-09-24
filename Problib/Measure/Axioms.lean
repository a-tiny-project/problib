import Problib.Measure.Pi.Axioms
import Problib.Measure.Giry.Axioms
import Problib.Measure.Memo.Axioms
import Problib.Measure.Normalization.Axioms
import Problib.Measure
import Problib.Measure.Additive.Axioms
import Problib.Measure.Approximation.Axioms
import Problib.Measure.AlmostEverywhere.Axioms
import Problib.Measure.Caratheodory.Axioms
import Problib.Measure.Coding.Axioms
import Problib.Measure.Convergence.Axioms
import Problib.Measure.Decomposition.Axioms
import Problib.Measure.Disintegration.Axioms
import Problib.Measure.Distribution.Axioms
import Problib.Measure.Dynkin.Axioms
import Problib.Measure.Equivalence.Axioms
import Problib.Measure.Embedding.Axioms
import Problib.Measure.Extended.Axioms
import Problib.Measure.Integral.Axioms
import Problib.Measure.Kernel.Axioms
import Problib.Measure.Necessity.Axioms
import Problib.Measure.Null.Axioms
import Problib.Measure.Outer.Axioms
import Problib.Measure.Product.Axioms
import Problib.Measure.Real.Axioms
import Problib.Measure.Set.Axioms
import Problib.Measure.Space.Axioms
import Problib.Measure.StandardBorel.Axioms
import Problib.Measure.TotalVariation.Axioms
import Problib.Measure.Uniform.Axioms
import Trust.Command

#audit_registered_claims

#audit_package [Problib.Measure] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
