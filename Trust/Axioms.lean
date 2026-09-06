import Trust

#audit_package [Trust] allowing [propext, Quot.sound, Classical.choice]

#audit_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Trust.addClaimGroup,
  Trust.claimGroups,
  Trust.Policy.create,
  Trust.Policy.permits,
  Trust.auditClaim,
  Trust.auditPackage,
  Trust.renderClaims
]
