import Foundations.Real
import Foundations.Real.Additive.Axioms
import Foundations.Real.Approximation.Axioms
import Foundations.Real.Basis.Axioms
import Foundations.Real.Coding.Axioms
import Foundations.Real.Extended.Axioms
import Foundations.Real.Inverse.Axioms
import Foundations.Real.Multiplicative.Axioms
import Foundations.Real.Nonnegative.Axioms
import Foundations.Real.Series.Axioms
import Foundations.Real.Construction.Dedekind.AdditiveSelection.Axioms
import Foundations.Real.Construction.Dedekind.MultiplicativeSelection.Axioms
import Foundations.Real.Construction.Dedekind.Selection.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.Real.Necessity.noGreatestPremiseNecessary,
  Foundations.Real.Necessity.orderEmbeddingNeedNotPreserveAddition,
  Foundations.Real.Necessity.additiveGroupAndOrderNeedNotTranslateMonotonically,
  Foundations.Real.Necessity.multiplicationPreservationNeedNotPreserveOne,
  Foundations.Real.DedekindComplete.exists_glb
]

#audit_registered_claims

#audit_package [Foundations.Real] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
