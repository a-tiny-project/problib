import Lake

open Lake DSL

package foundations where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Foundations where

lean_lib Trust where

lean_lib TrustTest where
