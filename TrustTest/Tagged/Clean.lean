import Trust

namespace TrustTest.Tagged.Clean

@[trust_claim]
theorem plain : True :=
  True.intro

@[trust_claim]
theorem choose {α : Sort _} (h : Nonempty α) :
    ∃ value : α, value = value :=
  ⟨Classical.choice h, rfl⟩

end TrustTest.Tagged.Clean
