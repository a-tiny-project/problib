module

public import Lean.Attributes

public section

namespace Trust

open Lean

/-- `@[trust_claim]` registers a declaration as an audited claim in the module
that declares it, so the tag shows in the claim's own diff. A private name is
refused because a module's export omits private entries, and the audit would
never see it. -/
initialize claimAttribute : TagAttribute ←
  registerTagAttribute `trust_claim
    "register a declaration as an audited trust claim"
    (validate := fun declaration => do
      if isPrivateName declaration then
        throwError m!"trust audit: claim {privateToUserName declaration} is private")

end Trust
