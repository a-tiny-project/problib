import Foundations.QuasiBorel.Domain.Axioms
import Foundations.QuasiBorel.Pi.Axioms
import Foundations.QuasiBorel.Sum.Axioms
import Foundations.QuasiBorel
import Foundations.QuasiBorel.Measurable.Axioms
import Foundations.QuasiBorel.Probability.Axioms
import Foundations.QuasiBorel.SFinite.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Foundations.QuasiBorel.Space.subtype,
  Foundations.QuasiBorel.Space.subtype_random_iff,
  Foundations.QuasiBorel.Space.subtypeVal,
  Foundations.QuasiBorel.Space.subtypeVal_apply,
  Foundations.QuasiBorel.Space.subtypeVal_injective,
  Foundations.QuasiBorel.Hom.subtypeLift,
  Foundations.QuasiBorel.Hom.subtypeLift_apply,
  Foundations.QuasiBorel.Hom.subtypeVal_subtypeLift,
  Foundations.QuasiBorel.Hom.subtypeLift_unique
]

#audit_registered_claims

#audit_package [Foundations.QuasiBorel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
