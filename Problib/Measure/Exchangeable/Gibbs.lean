module

public import Problib.Measure.Exchangeable.Site
public import Problib.Measure.Exchangeable.Finite
public import Problib.Measure.Kernel.Site.Finite
public import Problib.Measure.AlmostEverywhere.Transport

set_option autoImplicit false

/-!
# Site Gibbs at an exchangeable urn

At slot `i` of `n + 1` draws, an exchangeable urn's view disintegrates into the
view of `n` draws, followed by a finite reinsertion at the slot
(`Exchangeable.site_disintegration`). The context is the view with the slot's
item deleted. The reinsertions are the slots of the urn's finite draw kernel at
the context's statistic, each weighted by the kernel's mass there. The
insertion is the site transport's. The proof reads the history law one draw at
a time, moves the new draw to slot `i` by the transport, and moves it back by
exchangeability.

The site move of `Kernel.Site.FiniteSite` at this disintegration therefore
leaves the view's law invariant (`Exchangeable.site_invariant`). Pointwise, the
view's mass at an insertion is the mass at the context times the predictive at
the slot (`Exchangeable.site_mass`), which is `chain_site` read through
`law_unique`.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Kernel.Site

public section

universe v w

variable {U : Urn.{0, v} (Space.discrete Nat)} {S : U.Sampled}
  {W : View.{0, w} (Space.discrete Nat)}

/-- The statistic of a view's representative history. -/
@[expose] def SiteTransport.stat (T : SiteTransport U W) (n : Nat) (c : W.V n) : U.Stat :=
  U.stat U.init (toList (T.rep n c))

/-- The urn's site at slot `i` of `n + 1` draws: delete the slot's item from the
view, and reinsert at each slot of the finite kernel at the context's statistic,
weighted by the kernel's mass there. -/
@[expose] noncomputable def Urn.Finite.site (F : U.Finite S) (T : SiteTransport U W)
    (discrete : ∀ n set, (W.space n).Measurable set)
    (inSlot : ∀ n c a, S.Valid (T.stat n c) → a ∈ F.slots (T.stat n c) → T.Slot n c a)
    (deleteInsert : ∀ n i c a, T.Slot n c a → W.deleteView n i (T.insert n i c a) = c)
    (n : Nat) (i : Fin (n + 1)) (bound : Nat)
    (slots_length : ∀ c, (F.slots (T.stat n c)).length ≤ bound) :
    FiniteSite (W.space (n + 1)) (W.space n) Nat where
  delete := W.deleteView n i
  delete_measurable := W.deleteView_measurable n i
  context_discrete := discrete n
  insert c a := T.insert n i c a
  slots c := F.slots (T.stat n c)
  bound := bound
  slots_length := slots_length
  weight c a := ENNReal.finitePart (S.kernel (T.stat n c) (· = a))
  Valid c := S.Valid (T.stat n c)
  delete_insert valid a member := deleteInsert n i _ a (inSlot n _ a valid member)

variable (E : Exchangeable U S W) (T : SiteTransport U W) (F : U.Finite S)
  (discrete : ∀ n set, (W.space n).Measurable set) (counting : S.base = Measure.counting)
  (inSlot : ∀ n c a, S.Valid (T.stat n c) → a ∈ F.slots (T.stat n c) → T.Slot n c a)
  (deleteInsert : ∀ n i c a, T.Slot n c a → W.deleteView n i (T.insert n i c a) = c)

include counting in
/-- Almost every history from the initial statistic is positive, with a valid
statistic. -/
private theorem law_positive_valid (n : Nat) :
    (U.law S U.init n).AE fun ys =>
      U.chain U.init (toList ys) ≠ ENNReal.zero ∧ S.Valid (U.stat U.init (toList ys)) := by
  classical
  refine Measure.AE.and ?_ (Urn.law_valid S S.valid_init n)
  exact Urn.law_null S counting n fun ys failing => Classical.byContradiction failing

include discrete counting in
/-- Almost every context under the view of `n` draws has a valid statistic. -/
theorem SiteTransport.view_valid (n : Nat) :
    ((U.law S U.init n).map (W.view n) (W.view_measurable n)).AE fun c => S.Valid (T.stat n c) := by
  rw [Measure.ae_map_iff _ _ (discrete n _)]
  refine (law_positive_valid counting n).mono fun ys good => ?_
  change S.Valid (U.stat U.init (toList (T.rep n (W.view n ys))))
  rw [← T.canonical n ys good.1]
  exact good.2

include F discrete inSlot in
/-- At a valid context, the kernel's mass on the draws that the transport and
exchangeability send into `set` is the site's reinsertion mass on `set`. -/
private theorem kernel_site (n : Nat) (i : Fin (n + 1)) (bound slots_length) {c : W.V n}
    (valid : S.Valid (T.stat n c)) (set : Set (W.V (n + 1))) :
    S.kernel (T.stat n c)
        (fun a => set (W.act (n + 1) (Perm.toLast i).symm (W.view (n + 1) (snoc (T.rep n c) a)))) =
      (F.site T discrete inSlot deleteInsert n i bound slots_length).mass c set := by
  change _ = FiniteSite.spread _ c _ set
  rw [F.decomp valid, Measure.listSum_apply _ (Space.discrete_measurable _),
    FiniteSite.spread_apply _ c _ (discrete _ set), List.map_map]
  refine ENNReal.additiveLaws.listSum_map_congr _ fun a member => ?_
  change Measure.smul _ _ _ = ENNReal.mul (ENNReal.finite (ENNReal.finitePart _)) _
  rw [Measure.smul_apply_measurable _ _ (Space.discrete_measurable _),
    ENNReal.finite_finitePart (ENNReal.finite_iff_ne_top.mp
      (ENNReal.finite_of_le ((S.markov valid).apply_le_one _) True.intro))]
  have key := T.act_snoc n i c a (inSlot n c a valid member)
  by_cases inside : set (T.insert n i c a)
  · rw [Measure.dirac_apply_of_mem (Space.discrete Nat) a (Space.discrete_measurable _)
        (show set (W.act (n + 1) (Perm.toLast i).symm (W.view (n + 1) (snoc (T.rep n c) a)))
          by rw [key]; exact inside),
      Measure.dirac_apply_of_mem (W.space (n + 1))
        ((F.site T discrete inSlot deleteInsert n i bound slots_length).insert c a)
        (discrete _ set) inside]
  · rw [Measure.dirac_apply_of_not_mem (Space.discrete Nat) a (Space.discrete_measurable _)
        (show ¬set (W.act (n + 1) (Perm.toLast i).symm (W.view (n + 1) (snoc (T.rep n c) a)))
          by rw [key]; exact inside),
      Measure.dirac_apply_of_not_mem (W.space (n + 1))
        ((F.site T discrete inSlot deleteInsert n i bound slots_length).insert c a)
        (discrete _ set) inside]

include E F discrete counting inSlot in
/-- X5 at an exchangeable urn, sum form: the view of `n + 1` draws is the view of
`n` draws followed by the finite reinsertion at slot `i`. -/
theorem Exchangeable.site_disintegration (n : Nat) (i : Fin (n + 1)) (bound : Nat)
    (slots_length : ∀ c, (F.slots (T.stat n c)).length ≤ bound) :
    (U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)) =
      ((U.law S U.init n).map (W.view n) (W.view_measurable n)).bind
        (F.site T discrete inSlot deleteInsert n i bound slots_length).mass := by
  apply Measure.ext
  intro set measurable
  rw [← E.exchange (n + 1) (Perm.toLast i).symm, Measure.map_apply _ _ _ measurable,
    Measure.map_apply _ _ _ (discrete _ _), Urn.law_succ,
    Measure.map_apply _ _ _ (historySpace_nat_measurable _ _)]
  refine (Measure.semiproduct_apply _ _ _
    (snoc_measurable _ n (historySpace_nat_measurable _ _))).trans ?_
  rw [Measure.bind_apply _ _ measurable,
    lintegral_map _ _ _ (FiniteSite.measurable_of_discrete (discrete n) _)]
  refine lintegral_congr_ae ((law_positive_valid counting n).mono fun ys good => ?_)
  have canonical := T.canonical n ys good.1
  have valid : S.Valid (T.stat n (W.view n ys)) := by
    change S.Valid (U.stat U.init (toList (T.rep n (W.view n ys))))
    rw [← canonical]
    exact good.2
  refine Eq.trans ?_ (kernel_site T F discrete inSlot deleteInsert n i bound slots_length valid set)
  change S.kernel (U.stat U.init (toList ys)) _ =
    S.kernel (U.stat U.init (toList (T.rep n (W.view n ys)))) _
  rw [← canonical]
  rfl

include E F discrete counting inSlot deleteInsert in
/-- The site move at an exchangeable urn leaves the view law invariant, whatever
it does at total zero. -/
theorem Exchangeable.site_invariant (n : Nat) (i : Fin (n + 1)) (bound : Nat)
    (slots_length : ∀ c, (F.slots (T.stat n c)).length ≤ bound)
    (fallback : Kernel (W.space (n + 1)) (W.space (n + 1))) :
    ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1))).bind
        ((F.site T discrete inSlot deleteInsert n i bound slots_length).kernel fallback) =
      (U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1)) :=
  FiniteSite.kernel_invariant _
    (E.site_disintegration T F discrete counting inSlot deleteInsert n i bound slots_length)
    (T.view_valid discrete counting n) fallback

include E F discrete counting inSlot in
/-- X5 at an exchangeable urn's posterior: a view density that factors at slot
`i`, an outer factor of the context times a local factor of the slot, reweights
the site disintegration. -/
theorem Exchangeable.collapsed_site (n : Nat) (i : Fin (n + 1)) (bound : Nat)
    (slots_length : ∀ c, (F.slots (T.stat n c)).length ≤ bound)
    {density : W.V (n + 1) → ENNReal} {outer : W.V n → ENNReal} {factor : W.V n → Nat → NNReal}
    (factors : ∀ c, S.Valid (T.stat n c) → ∀ a ∈ F.slots (T.stat n c),
      density (T.insert n i c a) = ENNReal.mul (outer c) (ENNReal.finite (factor c a))) :
    ((U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1))).withDensity
        density =
      (((U.law S U.init n).map (W.view n) (W.view_measurable n)).withDensity outer).bind
        ((F.site T discrete inSlot deleteInsert n i bound slots_length).reweight factor).mass :=
  FiniteSite.withDensity_sum _
    (E.site_disintegration T F discrete counting inSlot deleteInsert n i bound slots_length)
    (T.view_valid discrete counting n)
    (FiniteSite.measurable_of_discrete (C := W.space (n + 1)) (discrete (n + 1)) density) factors

include counting in
/-- The view's mass at a fixed value is the chain at its representative. -/
private theorem view_mass (single : ∀ n (value : W.V n), (W.space n).Measurable (· = value))
    (n : Nat) (value : W.V n)
    (fixed : W.view n (T.rep n value) = value) :
    (U.law S U.init n).map (W.view n) (W.view_measurable n) (· = value) =
      U.chain U.init (toList (T.rep n value)) := by
  rw [Measure.map_apply _ _ _ (single n value)]
  apply Urn.law_unique S counting n fixed
  intro ys inside nonzero
  exact (T.canonical n ys nonzero).trans (congrArg (T.rep n) inside)

include E counting in
/-- X5 at an exchangeable urn, pointwise: the view's mass at an insertion is the
mass at the context times the predictive at the slot. -/
theorem Exchangeable.site_mass (single : ∀ n (value : W.V n), (W.space n).Measurable (· = value))
    (n : Nat)
    (i : Fin (n + 1)) (c : W.V n) (a : Nat) (fixed : W.view n (T.rep n c) = c)
    (slot : T.Slot n c a)
    (positive : U.chain U.init (toList (snoc (T.rep n c) a)) ≠ ENNReal.zero) :
    (U.law S U.init (n + 1)).map (W.view (n + 1)) (W.view_measurable (n + 1))
        (· = T.insert n i c a) =
      ENNReal.mul ((U.law S U.init n).map (W.view n) (W.view_measurable n) (· = c))
        (U.predictive (T.stat n c) a) := by
  rw [view_mass T counting single (n + 1) _ (T.insert_view n i c a slot),
    view_mass T counting single n c fixed,
    chain_site E T counting single n i c a slot positive]
  rfl

end

end Problib.Measure.Exchangeable
