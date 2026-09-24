import Problib.QuasiBorel.Domain.Axioms
import Problib.QuasiBorel.Pi.Axioms
import Problib.QuasiBorel.Sum.Axioms
import Problib.QuasiBorel
import Problib.QuasiBorel.List
import Problib.QuasiBorel.Measurable.Axioms
import Problib.QuasiBorel.Probability.Axioms
import Problib.QuasiBorel.SFinite.Axioms
import Trust.Command

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.QuasiBorel.Space.subtype,
  Problib.QuasiBorel.Space.subtype_random_iff,
  Problib.QuasiBorel.Space.subtypeVal,
  Problib.QuasiBorel.Space.subtypeVal_apply,
  Problib.QuasiBorel.Space.subtypeVal_injective,
  Problib.QuasiBorel.Hom.subtypeLift,
  Problib.QuasiBorel.Hom.subtypeLift_apply,
  Problib.QuasiBorel.Hom.subtypeVal_subtypeLift,
  Problib.QuasiBorel.Hom.subtypeLift_unique,
  Problib.QuasiBorel.Space.list,
  Problib.QuasiBorel.Space.listCons,
  Problib.QuasiBorel.Space.listView,
  Problib.QuasiBorel.Space.listFoldAt,
  Problib.QuasiBorel.Space.listFoldAt_apply,
  Problib.QuasiBorel.Space.listFold,
  Problib.QuasiBorel.Space.listFold_apply
]

#audit_registered_claims

#audit_package [Problib.QuasiBorel] allowing [
  propext,
  Quot.sound,
  Classical.choice
]
