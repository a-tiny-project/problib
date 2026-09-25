import Trust
import TrustTest.Registry.Alpha

namespace TrustTest.Registry.Beta

theorem propositional {left right : Prop} (h : left ↔ right) :
    left = right :=
  propext h

#register_trust_claims allowing [propext] claims [
  TrustTest.Registry.Beta.propositional
]

end TrustTest.Registry.Beta
