import Trust

namespace TrustTest.Allowed

theorem usesPropext {left right : Prop} (h : left ↔ right) :
    left = right :=
  propext h

theorem usesQuotSound {α : Sort _} {relation : α → α → Prop}
    (left right : α) (h : relation left right) :
    Quot.mk relation left = Quot.mk relation right :=
  Quot.sound h

theorem usesChoice {α : Sort _} (h : Nonempty α) :
    ∃ value : α, value = value :=
  ⟨Classical.choice h, rfl⟩

/--
info: trust package TrustTest.Allowed: 3 declarations, axioms [propext, Classical.choice, Quot.sound]
-/
#guard_msgs(info) in
#audit_package [TrustTest.Allowed] allowing [
  propext,
  Quot.sound,
  Classical.choice
]

/--
info: trust claim TrustTest.Allowed.usesChoice: axioms [Classical.choice]
---
info: trust claim TrustTest.Allowed.usesPropext: axioms [propext]
---
info: trust claim TrustTest.Allowed.usesQuotSound: axioms [Quot.sound]
-/
#guard_msgs(info) in
#audit_claims allowing [
  propext,
  Quot.sound,
  Classical.choice
] claims [
  TrustTest.Allowed.usesQuotSound,
  TrustTest.Allowed.usesChoice,
  TrustTest.Allowed.usesPropext
]

end TrustTest.Allowed
