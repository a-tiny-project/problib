import Trust

namespace TrustTest.Registry.Alpha

theorem choose {α : Sort _} (h : Nonempty α) :
    ∃ value : α, value = value :=
  ⟨Classical.choice h, rfl⟩

#register_trust_claims allowing [Classical.choice] claims [
  TrustTest.Registry.Alpha.choose
]

end TrustTest.Registry.Alpha
