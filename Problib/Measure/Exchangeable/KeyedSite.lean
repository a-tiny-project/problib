module

public import Problib.Measure.Exchangeable.Keyed

set_option autoImplicit false

/-!
# The keyed chain at a site

A keyed urn keeps one copy of an urn at each natural-number key. From the
initial statistic its chain does not see an injective relabeling of the keys
(`Urn.keyed_chain_relabel`): each relabeled observation reads and moves the
copy its old key read and moved. With a local latent presentation the chain
does not see the order of the observations either (`Urn.Latent.chain_perm` at
`ofKeyed`). So at an insertion that relabels and reorders an appended
observation, the keyed chain is the chain before it times the keyed predictive
at the appended observation (`Urn.LocalLatent.keyed_insert`). This is the site
factor of a collapsed posterior whose density is a keyed chain.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Pi

public section

universe u v

variable {α : Type u} {Y : Space α}

namespace Urn

variable (B : Urn.{u, v} Y)

/-- Two keyed statistics that agree along a relabeling give the relabeled
observations the same chain. -/
private theorem keyed_chain_relabel_from {π : Nat → Nat} (relabel : Function.Injective π) :
    ∀ (pairs : List (Nat × α)) (s s' : Nat → B.Stat), (∀ k, s' (π k) = s k) →
      (B.keyed id Function.injective_id).chain s' (pairs.map fun p => (π p.1, p.2)) =
        (B.keyed id Function.injective_id).chain s pairs
  | [], _, _, _ => rfl
  | p :: rest, s, s', agree => by
      have head : B.predictive (s' (π p.1)) p.2 = B.predictive (s p.1) p.2 := by
        rw [agree p.1]
      have tail := keyed_chain_relabel_from relabel rest
        (replace s p.1 (B.incorporate (s p.1) p.2))
        (replace s' (π p.1) (B.incorporate (s' (π p.1)) p.2)) fun k => by
          by_cases same : k = p.1
          · rw [same, replace_same, replace_same, agree p.1]
          · rw [replace_other _ _ (relabel.ne same), replace_other _ _ same, agree k]
      show ENNReal.mul (B.predictive (s' (π p.1)) p.2)
          ((B.keyed id Function.injective_id).chain
            (replace s' (π p.1) (B.incorporate (s' (π p.1)) p.2)) (rest.map fun p => (π p.1, p.2))) =
        ENNReal.mul (B.predictive (s p.1) p.2)
          ((B.keyed id Function.injective_id).chain (replace s p.1 (B.incorporate (s p.1) p.2)) rest)
      exact congr (congrArg ENNReal.mul head) tail

/-- From the initial statistic the keyed chain does not see an injective
relabeling of the keys. -/
theorem keyed_chain_relabel {π : Nat → Nat} (relabel : Function.Injective π)
    (pairs : List (Nat × α)) :
    (B.keyed id Function.injective_id).chain (B.keyed id Function.injective_id).init
        (pairs.map fun p => (π p.1, p.2)) =
      (B.keyed id Function.injective_id).chain (B.keyed id Function.injective_id).init pairs :=
  B.keyed_chain_relabel_from relabel pairs _ _ fun _ => rfl

/-- At an insertion that relabels the keys injectively and reorders an appended
observation, the keyed chain is the chain before it times the keyed predictive
at the appended observation. -/
theorem LocalLatent.keyed_insert {B : Urn.{u, v} Y} (L : B.LocalLatent) {π : Nat → Nat}
    (relabel : Function.Injective π) {pairs inserted : List (Nat × α)} (extra : Nat × α)
    (moved : ((pairs ++ [extra]).map fun p => (π p.1, p.2)).Perm inserted) :
    (B.keyed id Function.injective_id).chain (B.keyed id Function.injective_id).init inserted =
      ENNReal.mul
        ((B.keyed id Function.injective_id).chain (B.keyed id Function.injective_id).init pairs)
        ((B.keyed id Function.injective_id).predictive
          ((B.keyed id Function.injective_id).stat (B.keyed id Function.injective_id).init pairs)
          extra) := by
  rw [← (L.ofKeyed id Function.injective_id).chain_perm
      (L.ofKeyed id Function.injective_id).valid_init moved,
    B.keyed_chain_relabel relabel, Urn.chain_snoc]

end Urn

end

end Problib.Measure.Exchangeable
