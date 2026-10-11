module

public import Problib.Measure.Exchangeable.Density
public import Problib.Measure.Exchangeable.Latent
public import Problib.Measure.Exchangeable.Power

set_option autoImplicit false

/-!
# Witnesses of exchangeability

A sampled urn is exchangeable for a view when every permutation acting on the
view of its history law leaves that law unchanged. Exchangeability of the raw
history gives it for every view (`Exchangeable.of_raw`), because a view is
equivariant. A latent presentation of the urn witnesses it: the chain's mass
does not depend on the order of the observations (`Witness.latent_chain`), the
history law is the base power with the chain as its density, and permutations
leave the base power unchanged (`Witness.latent_raw`). A `Witness` is either a
latent presentation or a direct proof, and each gives exchangeability
(`Witness.exchangeable`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v w

variable {α : Type u} {Y : Space α}

/-- Every permutation leaves the view of the history law from the initial
statistic unchanged. -/
structure Exchangeable (U : Urn.{u, v} Y) (S : U.Sampled) (W : View.{u, w} Y) : Prop where
  exchange : ∀ (n : Nat) (σ : Perm n),
    ((U.law S U.init n).map (W.view n) (W.view_measurable n)).map (W.act n σ)
        (W.act_measurable n σ) =
      (U.law S U.init n).map (W.view n) (W.view_measurable n)

/-- A latent presentation of an urn, or a direct proof that it is exchangeable. -/
inductive Witness (U : Urn.{u, v} Y) (S : U.Sampled) (W : View.{u, w} Y) : Type (max u (v + 1))
  | latent (L : U.Latent)
  | sampled (E : Exchangeable U S W)

/-- The listed history of a permuted history is a reordering of the listed
history. -/
theorem toList_permute {n : Nat} (σ : Perm n) (ys : Fin n → α) :
    (toList (permute σ ys)).Perm (toList ys) := by
  have slots : (List.ofFn fun index : Fin n => index).Nodup := List.nodup_finRange n
  have nodup : (List.ofFn σ.inverse).Nodup := by
    have mapped := List.Pairwise.map (R := (· ≠ ·)) (S := (· ≠ ·)) σ.inverse
      (fun a b different equal => different (by
        rw [← σ.forward_inverse a, ← σ.forward_inverse b, equal])) slots
    rw [List.map_ofFn] at mapped
    exact mapped
  have reordered : (List.ofFn σ.inverse).Perm (List.ofFn fun index : Fin n => index) := by
    rw [List.perm_ext_iff_of_nodup nodup slots]
    intro a
    simp only [List.mem_ofFn]
    exact ⟨fun _ => ⟨a, rfl⟩, fun _ => ⟨σ.forward a, σ.inverse_forward a⟩⟩
  have mapped := reordered.map ys
  rw [List.map_ofFn, List.map_ofFn] at mapped
  exact mapped

namespace Witness

variable {U : Urn.{u, v} Y}

/-- Under a latent presentation the chain's mass does not depend on the order
of the observations. -/
theorem latent_chain (L : U.Latent) {q : U.Stat} (valid : L.Valid q) {ys ys' : List α}
    (perm : ys.Perm ys') : U.chain q ys = U.chain q ys' := by
  have total : ∀ zs : List α, (L.prior.kernel q).withDensity (L.evidence zs) Set.univ =
      U.chain q zs := by
    intro zs
    rw [L.collapse valid zs, Measure.smul_apply_measurable _ _ (Space.univ _),
      (L.prior.markov _).univ_eq_one, ENNReal.mul_one]
  rw [← total ys, ← total ys', L.evidence_perm perm]

/-- A latent presentation makes the raw history exchangeable. -/
theorem latent_raw (L : U.Latent) (S : U.Sampled) : Exchangeable U S (View.raw Y) := by
  constructor
  intro n σ
  change ((U.law S U.init n).map (fun ys => ys) (MeasurableMap.identity _)).map (permute σ)
      (permute_measurable Y σ) = (U.law S U.init n).map (fun ys => ys) (MeasurableMap.identity _)
  rw [Measure.map_id, Urn.law_eq_density S S.valid_init n]
  have invariant : (fun ys => U.chain U.init (toList ys)) =
      fun ys => U.chain U.init (toList (permute σ ys)) :=
    funext fun ys => (latent_chain L L.valid_init (toList_permute σ ys)).symm
  conv => lhs; rw [invariant]
  rw [Measure.map_withDensity _ _ (permute_measurable Y σ) (U.chain_measurable U.init n),
    power_permute]

end Witness

/-- Exchangeability of the raw history gives exchangeability for every view. -/
theorem Exchangeable.of_raw {U : Urn.{u, v} Y} {S : U.Sampled}
    (E : Exchangeable U S (View.raw Y)) (W : View.{u, w} Y) : Exchangeable U S W := by
  constructor
  intro n σ
  have raw := E.exchange n σ
  change ((U.law S U.init n).map (fun ys => ys) (MeasurableMap.identity _)).map (permute σ)
      (permute_measurable Y σ) = (U.law S U.init n).map (fun ys => ys) (MeasurableMap.identity _)
    at raw
  rw [Measure.map_id] at raw
  rw [Measure.map_comp]
  have equivariant : (fun ys => W.act n σ (W.view n ys)) = fun ys => W.view n (permute σ ys) :=
    funext fun ys => (W.equivariant n σ ys).symm
  rw [map_congr_function _ equivariant _
    (MeasurableMap.comp (W.view_measurable n) (permute_measurable Y σ)),
    ← Measure.map_comp _ _ _ (permute_measurable Y σ) (W.view_measurable n), raw]

/-- Each witness gives exchangeability. -/
theorem Witness.exchangeable {U : Urn.{u, v} Y} {S : U.Sampled} {W : View.{u, w} Y} :
    Witness U S W → Exchangeable U S W
  | .latent L => (Witness.latent_raw L S).of_raw W
  | .sampled E => E

end

end Problib.Measure.Exchangeable
