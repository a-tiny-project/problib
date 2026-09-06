import Trust
import TrustTest.Registry.Alpha

namespace TrustTest.Registry.Gamma

theorem quotient {α : Sort _} {relation : α → α → Prop}
    (left right : α) (h : relation left right) :
    Quot.mk relation left = Quot.mk relation right :=
  Quot.sound h

#register_trust_claims allowing [Quot.sound] claims [
  TrustTest.Registry.Gamma.quotient
]

end TrustTest.Registry.Gamma
