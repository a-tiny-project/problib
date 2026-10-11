module

public import Problib.Measure.Kernel.Site
public import Problib.Measure.Kernel.Iteration.Ergodic
public import Problib.FiniteEnumeration
import Problib.Measure.Kernel.Composition.Bind.Transport

/-! Convergence of systematic scans.

A scan runs one update per listed site. Refreshing a site draws it from a fixed
reference law whatever the point is. Refreshing every site forgets the start,
and the result is the law that draws each site from its reference.

A step whose kernel keeps `weight` of the reference at its site dominates the
refresh of that site scaled by `weight`. Domination survives composition, so a
scan of `n` such steps dominates `weight ^ n` times the refresh of its sites.
When the scan visits every site this is a one-sweep minorization, and the scan
converges in total variation from every law to each law it leaves invariant.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Site

open Problib.Real

universe u v

variable {ι : Type u} {α : ι → Type v} {spaces : ∀ index, Space (α index)}

/-- The step that draws `site` from `measure` wherever the point is. -/
@[expose] public noncomputable def Step.const (site : ι) (measure : Measure (spaces site))
    (finite : Measure.SFinite measure) : Step spaces where
  site := site
  kernel := Kernel.const (Space.pi spaces) measure
  finite := IsSFinite.const (Space.pi spaces) finite

/-- `weight ^ count` in the nonnegative reals, the weight that a sweep of
`count` steps keeps. -/
@[expose] public noncomputable def sweepWeight (weight : NNReal) : Nat → NNReal
  | 0 => NNReal.one
  | count + 1 => NNReal.mul weight (sweepWeight weight count)

private theorem sweepWeight_finite (weight : NNReal) (count : Nat) :
    ENNReal.finite (sweepWeight weight count) = ENNReal.pow (ENNReal.finite weight) count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [sweepWeight, ← ENNReal.finite_mul_finite, induction, ENNReal.pow_succ]

private theorem sweepWeight_positive {weight : NNReal} (positive : NNReal.lt NNReal.zero weight)
    (count : Nat) : NNReal.lt NNReal.zero (sweepWeight weight count) := by
  induction count with
  | zero => exact NNReal.one_positive
  | succ count induction => exact NNReal.mul_positive positive induction

private theorem sweepWeight_le_one {weight : NNReal} (atMostOne : NNReal.le weight NNReal.one)
    (count : Nat) : NNReal.le (sweepWeight weight count) NNReal.one := by
  induction count with
  | zero => exact NNReal.le_refl _
  | succ count induction =>
      have bound := NNReal.mul_le_mul atMostOne induction
      rw [NNReal.mul_one] at bound
      exact bound

variable [DecidableEq ι]

public theorem Step.const_run_apply (site : ι) (measure : Measure (spaces site))
    (finite : Measure.SFinite measure) (point : ∀ index, α index) :
    (Step.const site measure finite).run point =
      measure.map (replace point site) (replace_value_measurable point site) :=
  update_apply site _ _ point

/-- Refreshing a site from a probability law twice is refreshing it once. -/
public theorem Step.const_run_comp_self (site : ι) {measure : Measure (spaces site)}
    (finite : Measure.SFinite measure) (probability : Measure.IsProbability measure) :
    (Step.const site measure finite).run.comp (Step.const site measure finite).run =
      (Step.const site measure finite).run := by
  apply Kernel.ext
  intro point
  have constant : (Step.const site measure finite).run.precomp (replace point site)
      (replace_value_measurable point site) =
      Kernel.const (spaces site)
        (measure.map (replace point site) (replace_value_measurable point site)) := by
    apply Kernel.ext
    intro value
    rw [Kernel.precomp_apply, Step.const_run_apply, Kernel.const_apply]
    congr 1
    funext other
    exact replace_replace_same point site value other
  rw [Kernel.comp_apply, Step.const_run_apply, Measure.bind_map, constant, Measure.bind_const,
    probability.univ_eq_one, Measure.one_smul]

/-- Refresh the sites of `order` from their references, in order. -/
@[expose] public noncomputable def refresh (order : List ι)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    Kernel (Space.pi spaces) (Space.pi spaces) :=
  sweep (order.map (fun site => Step.const site (reference site) (referenceFinite site)))

public theorem refresh_cons (site : ι) (order : List ι)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    refresh (site :: order) reference referenceFinite =
      (Step.const site (reference site) (referenceFinite site)).run.comp
        (refresh order reference referenceFinite) :=
  rfl

public theorem refresh_singleton (site : ι) (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    refresh [site] reference referenceFinite =
      (Step.const site (reference site) (referenceFinite site)).run :=
  sweep_singleton _

public theorem refresh_append (first second : List ι)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    refresh (first ++ second) reference referenceFinite =
      (refresh first reference referenceFinite).comp
        (refresh second reference referenceFinite) := by
  unfold refresh
  rw [List.map_append, sweep_append]

/-- Refreshing distinct sites is the same kernel in every order. -/
public theorem refresh_perm {first second : List ι} (perm : first.Perm second)
    (nodup : first.Nodup) (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    refresh first reference referenceFinite = refresh second reference referenceFinite :=
  sweep_perm (perm.map _)
    (List.pairwise_map.mpr
      (List.Pairwise.imp (fun distinct => ⟨distinct, fun _ _ => rfl, fun _ _ => rfl⟩) nodup))

public theorem refresh_isProbability (order : List ι)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (point : ∀ index, α index) :
    Measure.IsProbability (refresh order reference referenceFinite point) := by
  apply sweep_isProbability
  intro step member _
  rcases List.mem_map.mp member with ⟨site, _, rfl⟩
  exact referenceProbability site

/-- A refresh reads only the sites it does not refresh. -/
public theorem refresh_reads (order : List ι) (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) :
    Reads (refresh order reference referenceFinite) (fun index => index ∉ order) := by
  induction order with
  | nil =>
      intro first second agree
      have same : first = second := funext (fun index => agree index (fun member => nomatch member))
      rw [same]
  | cons site rest induction =>
      intro first second agree
      rw [refresh_cons, Kernel.comp_apply, Kernel.comp_apply, Step.const_run_apply,
        Step.const_run_apply, Measure.bind_map, Measure.bind_map]
      congr 1
      apply Kernel.ext
      intro value
      rw [Kernel.precomp_apply, Kernel.precomp_apply]
      apply induction
      intro index outside
      by_cases equal : index = site
      · subst equal
        rw [replace_same, replace_same]
      · rw [replace_of_ne _ _ equal, replace_of_ne _ _ equal]
        exact agree index (fun member => (List.mem_cons.mp member).elim equal outside)

/-- A refresh of every site forgets the start. -/
public theorem refresh_eq_of_covers {order : List ι} (covers : ∀ index, index ∈ order)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (first second : ∀ index, α index) :
    refresh order reference referenceFinite first =
      refresh order reference referenceFinite second :=
  refresh_reads order reference referenceFinite first second
    (fun index outside => absurd (covers index) outside)

/-- Refreshing every site once gives a law that refreshing any site again
leaves unchanged. -/
public theorem refresh_invariant {order : List ι} (sites : FiniteEnumeration order)
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (point : ∀ index, α index) (site : ι) :
    (refresh order reference referenceFinite point).bind
        (Step.const site (reference site) (referenceFinite site)).run =
      refresh order reference referenceFinite point := by
  have perm : order.Perm (order.erase site ++ [site]) :=
    (List.perm_cons_erase (sites.complete site)).trans
      (List.perm_append_singleton site (order.erase site)).symm
  rw [refresh_perm perm sites.nodup, refresh_append, refresh_singleton, Kernel.comp_apply,
    Measure.bind_assoc,
    Step.const_run_comp_self site (referenceFinite site) (referenceProbability site)]

private theorem update_refresh_lower {site : ι}
    {kernel : Kernel (Space.pi spaces) (spaces site)} (finite : IsSFinite kernel)
    {measure : Measure (spaces site)} (measureFinite : Measure.SFinite measure)
    {weight : ENNReal}
    (lower : ∀ point set, (spaces site).Measurable set →
      ENNReal.le (ENNReal.mul weight (measure set)) (kernel point set))
    (point : ∀ index, α index) {set : Set (∀ index, α index)}
    (setMeasurable : (Space.pi spaces).Measurable set) :
    ENNReal.le ((Measure.smul weight ((Step.const site measure measureFinite).run point)) set)
      (update site kernel finite point set) := by
  rw [Measure.smul_apply_measurable _ _ setMeasurable, Step.const_run_apply, update_apply,
    Measure.map_apply _ _ _ setMeasurable, Measure.map_apply _ _ _ setMeasurable]
  exact lower point _ (replace_value_measurable point site setMeasurable)

/-- A sweep whose kernels each keep `weight` of the reference at their site
dominates `weight ^ n` times the refresh of the same sites. -/
public theorem sweep_refresh_lower (steps : List (Step spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index)) {weight : ENNReal}
    (lower : ∀ step, step ∈ steps → ∀ point set, (spaces step.site).Measurable set →
      ENNReal.le (ENNReal.mul weight (reference step.site set)) (step.kernel point set))
    (point : ∀ index, α index) {set : Set (∀ index, α index)}
    (setMeasurable : (Space.pi spaces).Measurable set) :
    ENNReal.le
      (ENNReal.mul (ENNReal.pow weight steps.length)
        (refresh (steps.map Step.site) reference referenceFinite point set))
      (sweep steps point set) := by
  induction steps generalizing point with
  | nil =>
      rw [List.length_nil, ENNReal.pow_zero, ENNReal.one_mul]
      exact ENNReal.le_refl _
  | cons step rest induction =>
      have restMeasurable :=
        (refresh (rest.map Step.site) reference referenceFinite).measurable setMeasurable
      rw [List.map_cons, List.length_cons, refresh_cons, sweep_cons,
        comp_apply_measurable _ _ _ setMeasurable, comp_apply_measurable _ _ _ setMeasurable,
        ENNReal.pow_succ, ENNReal.mul_comm weight, ENNReal.mul_assoc, ← lintegral_smul_measure,
        ← lintegral_smul _ _ restMeasurable]
      exact ENNReal.le_trans
        (lintegral_mono_measure _ _ _ (fun region regionMeasurable =>
          update_refresh_lower step.finite (referenceFinite step.site)
            (lower step List.mem_cons_self) point regionMeasurable))
        (lintegral_mono _ (fun next => induction
          (fun other member => lower other (List.mem_cons_of_mem step member)) next))

/-- A scan that visits every site, of probability steps whose kernels each keep
`weight` of the reference at their site, is minorized in one sweep. The
reference law refreshes every site, and the weight is `weight ^ n` for `n`
steps. -/
public theorem sweep_minorization {steps : List (Step spaces)}
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (start : ∀ index, α index) (covers : ∀ index, index ∈ steps.map Step.site)
    (markov : ∀ step, step ∈ steps → ∀ point, Measure.IsProbability (step.kernel point))
    {weight : NNReal} (weightPositive : NNReal.lt NNReal.zero weight)
    (weightAtMostOne : NNReal.le weight NNReal.one)
    (lower : ∀ step, step ∈ steps → ∀ point set, (spaces step.site).Measurable set →
      ENNReal.le (ENNReal.mul (ENNReal.finite weight) (reference step.site set))
        (step.kernel point set)) :
    Minorization (sweep steps) 1 (sweepWeight weight steps.length)
      ⟨refresh (steps.map Step.site) reference referenceFinite start,
        refresh_isProbability _ reference referenceFinite referenceProbability start⟩ where
  markov := sweep_isProbability markov
  stepsPositive := Nat.zero_lt_one
  weightPositive := sweepWeight_positive weightPositive _
  weightAtMostOne := sweepWeight_le_one weightAtMostOne _
  lower := by
    intro input event eventMeasurable
    have bound := sweep_refresh_lower steps reference referenceFinite lower input eventMeasurable
    rw [refresh_eq_of_covers covers reference referenceFinite input start,
      ← sweepWeight_finite] at bound
    rw [iterate_one, Measure.smul_apply_measurable _ _ eventMeasurable]
    exact bound

/-- A scan as in `sweep_minorization` converges in total variation from every
law to each probability law it leaves invariant. -/
public theorem sweep_convergesFromEveryLaw {steps : List (Step spaces)}
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (covers : ∀ index, index ∈ steps.map Step.site)
    (markov : ∀ step, step ∈ steps → ∀ point, Measure.IsProbability (step.kernel point))
    {weight : NNReal} (weightPositive : NNReal.lt NNReal.zero weight)
    (weightAtMostOne : NNReal.le weight NNReal.one)
    (lower : ∀ step, step ∈ steps → ∀ point set, (spaces step.site).Measurable set →
      ENNReal.le (ENNReal.mul (ENNReal.finite weight) (reference step.site set))
        (step.kernel point set))
    (law : Giry.Law (Space.pi spaces)) (invariant : law.val.bind (sweep steps) = law.val) :
    ConvergesFromEveryLaw (sweep steps) law := by
  obtain ⟨start⟩ := law.property.nonempty
  exact minorization_convergesFromEveryLaw
    (sweep_minorization reference referenceFinite referenceProbability start covers markov
      weightPositive weightAtMostOne lower) law invariant

/-- `sweep_convergesFromEveryLaw` needs the scan to visit every site. On two
bits, the scan that only redraws the first bit from the Dirac measure at zero
keeps each point whose first bit is zero. The points `(0, 0)` and `(0, 1)` are
both invariant, so the scan converges from every law to no law. -/
public theorem unvisited_site_does_not_converge :
    ¬∃ law, ConvergesFromEveryLaw
      (sweep [Step.const (spaces := fun _ : Bool => Space.discrete Bool) false
        (Measure.dirac (Space.discrete Bool) false)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ false))]) law := by
  rintro ⟨law, converges⟩
  have fixed (bit : Bool) :
      (Measure.dirac (Space.pi (fun _ : Bool => Space.discrete Bool))
          (fun index => index && bit)).bind
        (sweep [Step.const (spaces := fun _ : Bool => Space.discrete Bool) false
          (Measure.dirac (Space.discrete Bool) false)
          (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ false))]) =
        Measure.dirac (Space.pi (fun _ : Bool => Space.discrete Bool))
          (fun index => index && bit) := by
    rw [Measure.dirac_bind, sweep_singleton, Step.const_run_apply, Measure.map_dirac]
    congr 1
    funext index
    cases index
    · exact replace_same _ _ _
    · exact replace_of_ne _ _ (show true ≠ false by decide)
  have atZero := converges.invariant_unique
    ⟨_, Measure.IsProbability.dirac _ (fun index => index && false)⟩ (fixed false)
  have atOne := converges.invariant_unique
    ⟨_, Measure.IsProbability.dirac _ (fun index => index && true)⟩ (fixed true)
  have setMeasurable : (Space.pi (fun _ : Bool => Space.discrete Bool)).Measurable
      (fun point : Bool → Bool => point true = true) :=
    Space.coordinate_measurable (fun _ : Bool => Space.discrete Bool) true
      (set := fun value : Bool => value = true) True.intro
  have evaluated := congrArg
    (fun law : Giry.Law (Space.pi (fun _ : Bool => Space.discrete Bool)) =>
      law.val (fun point : Bool → Bool => point true = true))
    (atZero.trans atOne.symm)
  simp only at evaluated
  rw [Measure.dirac_apply_of_not_mem _ _ setMeasurable (by decide),
    Measure.dirac_apply_of_mem _ _ setMeasurable (by decide)] at evaluated
  exact ENNReal.one_ne_zero evaluated.symm

end Problib.Measure.Kernel.Site
