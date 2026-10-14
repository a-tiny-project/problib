module

public import Problib.Measure.Exchangeable.Delete

set_option autoImplicit false

/-!
# The site factor of an exchangeable urn

Against a counting base each history of naturals has mass equal to its chain,
so a set of histories with one positive history has that history's chain as
its mass (`Urn.law_unique`), and a set of null histories has none
(`Urn.law_null`). A site transport names one history for each view value
(`rep`), which every positive history is (`canonical`), and an insertion of a
new observation at any slot of a view value (`insert`), which a permutation
carries to the view of the history with the observation appended
(`transport`). Exchangeability then moves the inserted observation to the
last slot without changing the view's mass, so the chain at an insertion is
the chain before it times the predictive at the inserted observation
(`chain_site`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Countable.Pair

public section

universe u v w

variable {α : Type u} {Y : Space α}

namespace Urn

variable {U : Urn.{0, v} (Space.discrete Nat)}

private theorem counting_atoms (S : U.Sampled) (counting : S.base = Measure.counting) :
    ∀ a, S.base (Set.singleton a) = ENNReal.one := fun a => by
  rw [counting]
  exact Measure.counting_singleton a

private theorem law_tsum (S : U.Sampled) (counting : S.base = Measure.counting) (n : Nat)
    (set : Set (Fin n → Nat)) :
    U.law S U.init n set = ENNReal.tsum fun code => match decodeHistory n code with
      | none => ENNReal.zero
      | some ys => ennrealIndicator set (fun ys => U.chain U.init (toList ys)) ys := by
  rw [law_eq_density S S.valid_init n,
    Measure.withDensity_apply _ _ (historySpace_nat_measurable n _),
    ← Measure.lintegral_indicator _ _ (historySpace_nat_measurable n _),
    power_lintegral S.base S.baseFinite (counting_atoms S counting) n]
  rfl

/-- Against a counting base, a set of histories whose one positive history is
`h` has the chain of `h` as its mass. -/
theorem law_unique (S : U.Sampled) (counting : S.base = Measure.counting) (n : Nat)
    {set : Set (Fin n → Nat)} {h : Fin n → Nat} (member : set h)
    (unique : ∀ ys, set ys → U.chain U.init (toList ys) ≠ ENNReal.zero → ys = h) :
    U.law S U.init n set = U.chain U.init (toList h) := by
  rw [law_tsum S counting n set, ENNReal.tsum_eq_of_at_most_one_nonzero _ (encodeTuple n h),
    decodeHistory_encode]
  · exact ennrealIndicator_of_mem member
  · intro code different
    cases decoded : decodeHistory n code with
    | none => rfl
    | some ys =>
        show ennrealIndicator set (fun ys => U.chain U.init (toList ys)) ys = ENNReal.zero
        by_cases inside : set ys
        · rw [ennrealIndicator_of_mem inside]
          by_cases zero : U.chain U.init (toList ys) = ENNReal.zero
          · exact zero
          · exact absurd (by rw [← encode_of_decodeHistory decoded, unique ys inside zero])
              different
        · exact ennrealIndicator_of_not_mem inside

/-- Against a counting base, a set of null histories has mass zero. -/
theorem law_null (S : U.Sampled) (counting : S.base = Measure.counting) (n : Nat)
    {set : Set (Fin n → Nat)}
    (null : ∀ ys, set ys → U.chain U.init (toList ys) = ENNReal.zero) :
    U.law S U.init n set = ENNReal.zero := by
  rw [law_tsum S counting n set]
  have each : ∀ code, (match decodeHistory n code with
      | none => ENNReal.zero
      | some ys => ennrealIndicator set (fun ys => U.chain U.init (toList ys)) ys) =
        ENNReal.zero := by
    intro code
    cases decodeHistory n code with
    | none => rfl
    | some ys =>
        show ennrealIndicator set (fun ys => U.chain U.init (toList ys)) ys = ENNReal.zero
        by_cases inside : set ys
        · rw [ennrealIndicator_of_mem inside]
          exact null ys inside
        · exact ennrealIndicator_of_not_mem inside
  rw [ENNReal.tsum_congr each]
  exact ENNReal.tsum_zero

end Urn

/-- One history for each view value, which every positive history is, and an
insertion of a new observation at a slot of a view value, which a permutation
carries to the view of the history with the observation appended. -/
structure SiteTransport (U : Urn.{u, v} Y) (W : View.{u, w} Y) where
  rep : (n : Nat) → W.V n → Fin n → α
  rep_view : ∀ n ys, W.view n (rep n (W.view n ys)) = W.view n ys
  canonical : ∀ n ys, U.chain U.init (toList ys) ≠ ENNReal.zero → ys = rep n (W.view n ys)
  Slot : (n : Nat) → W.V n → α → Prop
  insert : (n : Nat) → Fin (n + 1) → W.V n → α → W.V (n + 1)
  insert_view : ∀ n i v a, Slot n v a →
    W.view (n + 1) (rep (n + 1) (insert n i v a)) = insert n i v a
  transport : ∀ n i v a, Slot n v a →
    W.view (n + 1) (snoc (rep n v) a) = W.act (n + 1) (Perm.toLast i) (insert n i v a)

/-- Permuting back undoes a permutation. -/
theorem permute_symm_permute {β : Type u} {n : Nat} (σ : Perm n) (ys : Fin n → β) :
    permute σ.symm (permute σ ys) = ys :=
  funext fun index => congrArg ys (σ.inverse_forward index)

/-- Moving an insertion to the last slot and back gives the insertion. -/
theorem SiteTransport.act_snoc {U : Urn.{u, v} Y} {W : View.{u, w} Y} (T : SiteTransport U W)
    (n : Nat) (i : Fin (n + 1)) (v : W.V n) (a : α) (slot : T.Slot n v a) :
    W.act (n + 1) (Perm.toLast i).symm (W.view (n + 1) (snoc (T.rep n v) a)) =
      T.insert n i v a := by
  rw [T.transport n i v a slot]
  calc W.act (n + 1) (Perm.toLast i).symm (W.act (n + 1) (Perm.toLast i) (T.insert n i v a))
      = W.act (n + 1) (Perm.toLast i).symm (W.act (n + 1) (Perm.toLast i)
          (W.view (n + 1) (T.rep (n + 1) (T.insert n i v a)))) := by
        rw [T.insert_view n i v a slot]
    _ = W.view (n + 1) (permute (Perm.toLast i).symm
          (permute (Perm.toLast i) (T.rep (n + 1) (T.insert n i v a)))) := by
        rw [← W.equivariant, ← W.equivariant]
    _ = T.insert n i v a := by
        rw [permute_symm_permute, T.insert_view n i v a slot]

/-- At a valid slot whose appended history is positive, the chain at an
insertion is the chain before it times the predictive at the inserted
observation. -/
theorem chain_site {U : Urn.{0, v} (Space.discrete Nat)} {S : U.Sampled}
    {W : View.{0, w} (Space.discrete Nat)} (E : Exchangeable U S W) (T : SiteTransport U W)
    (counting : S.base = Measure.counting)
    (single : ∀ n (value : W.V n), (W.space n).Measurable (· = value))
    (n : Nat) (i : Fin (n + 1)) (v : W.V n) (a : Nat) (slot : T.Slot n v a)
    (positive : U.chain U.init (toList (snoc (T.rep n v) a)) ≠ ENNReal.zero) :
    U.chain U.init (toList (T.rep (n + 1) (T.insert n i v a))) =
      ENNReal.mul (U.chain U.init (toList (T.rep n v)))
        (U.predictive (U.stat U.init (toList (T.rep n v))) a) := by
  have mass : ∀ value : W.V (n + 1), W.view (n + 1) (T.rep (n + 1) value) = value →
      (U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)) (· = value) =
        U.chain U.init (toList (T.rep (n + 1) value)) := by
    intro value fixed
    rw [Measure.map_apply _ _ _ (single (n + 1) value)]
    apply Urn.law_unique S counting (n + 1) fixed
    intro ys inside nonzero
    exact (T.canonical (n + 1) ys nonzero).trans (congrArg (T.rep (n + 1)) inside)
  have moves : ∀ (τ : Perm (n + 1)) (p q : W.V (n + 1)), W.act (n + 1) τ p = q →
      ENNReal.le
        ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)) (· = p))
        ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)) (· = q)) := by
    intro τ p q moved
    have shift := Measure.map_apply
      ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)))
      (W.act (n + 1) τ) (W.act_measurable (n + 1) τ) (single (n + 1) q)
    rw [E.exchange (n + 1) τ] at shift
    rw [shift]
    apply Measure.mono
    intro value same
    change W.act (n + 1) τ value = q
    rw [same]
    exact moved
  have forward : W.act (n + 1) (Perm.toLast i) (T.insert n i v a) =
      W.view (n + 1) (snoc (T.rep n v) a) := (T.transport n i v a slot).symm
  have backward := T.act_snoc n i v a slot
  have equal := ENNReal.le_antisymm (moves _ _ _ forward) (moves _ _ _ backward)
  rw [mass _ (T.insert_view n i v a slot), mass _ (T.rep_view _ _),
    ← T.canonical (n + 1) _ positive] at equal
  rw [equal, toList_snoc, Urn.chain_snoc]

end

end Problib.Measure.Exchangeable
