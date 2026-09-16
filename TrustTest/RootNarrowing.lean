import Trust

/--
error: trust audit: package root roster is empty
-/
#guard_msgs(error) in
#audit_package [] allowing []

/--
error: trust audit: duplicate package roots [TrustTest.RootNarrowing]
-/
#guard_msgs(error) in
#audit_package [
  TrustTest.RootNarrowing,
  TrustTest.RootNarrowing
] allowing []

/--
error: trust audit: package audit for TrustTest.RootNarrowing must run from TrustTest.RootNarrowing.Axioms, not TrustTest.RootNarrowing
-/
#guard_msgs(error) in
#audit_package [TrustTest.RootNarrowing] allowing []
