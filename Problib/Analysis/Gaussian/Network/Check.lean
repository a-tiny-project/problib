module

public import Problib.Analysis.Gaussian.Network.Law

/-! Reading three runtime lists as a network, or naming why they are not one.

A model hands a network over as three lists: the intercepts `μ`, the
coefficient rows `B` and the innovation variances `d`. They form a network
exactly when they are `Shaped`: equal lengths, and row `i` of `B` holding `i`
coefficients. `triangularFailure` names the first place where they are not:

- `some k` with `k < n = |B|`: row `k` of `B` does not have `k` entries, and
  every earlier row is triangular;
- `some n`: every row is triangular, and `μ` or `d` does not have `n` entries;
- `none`: the lists are shaped (`triangularFailure_none`).

`checkedLaw` is the law of the runtime block that reads the three lists. A
failure at `k` is the point mass at `inl k`, so no draw is made and nothing
reads a ragged row as some other network. A shaped input draws from the
network's law into `inr` (`checkedLaw_shaped`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### The shape pass -/

/-- The first position, counted from `start`, of a row whose length is not its
position. -/
@[expose] public def triangularFrom : Nat → List (List Carrier) → Option Nat
  | _, [] => none
  | start, row :: rows =>
      if row.length = start then triangularFrom (start + 1) rows else some start

/-- The first row of `B` that is not triangular, or `|B|` when only the lengths
of `μ` or `d` are wrong. -/
@[expose] public def triangularFailure (intercept : List Carrier)
    (coefficients : List (List Carrier)) (variance : List Carrier) : Option Nat :=
  match triangularFrom 0 coefficients with
  | some row => some row
  | none =>
      if intercept.length = coefficients.length ∧ variance.length = coefficients.length then none
      else some coefficients.length

public theorem triangularFrom_none {start : Nat} {rows : List (List Carrier)} :
    triangularFrom start rows = none ↔
      ∀ (index : Nat) (row : List Carrier), rows[index]? = some row → row.length = start + index := by
  induction rows generalizing start with
  | nil => simp [triangularFrom]
  | cons first rest induction =>
      unfold triangularFrom
      split
      · rename_i counted
        rw [induction]
        constructor
        · intro later index row found
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              simpa using counted
          | succ index =>
              simp only [List.getElem?_cons_succ] at found
              rw [later index row found]
              omega
        · intro every index row found
          rw [every (index + 1) row (by simpa using found)]
          omega
      · rename_i wrong
        simp only [reduceCtorEq, false_iff, Classical.not_forall]
        exact ⟨0, first, by simp, by simpa using wrong⟩

public theorem triangularFrom_some {start position : Nat} {rows : List (List Carrier)}
    (found : triangularFrom start rows = some position) :
    start ≤ position ∧ position - start < rows.length ∧
      (rows.getD (position - start) []).length ≠ position ∧
      ∀ index, index < position - start → (rows.getD index []).length = start + index := by
  induction rows generalizing start with
  | nil => cases found
  | cons first rest induction =>
      unfold triangularFrom at found
      split at found
      · rename_i counted
        obtain ⟨after, below, wrong, earlier⟩ := induction found
        refine ⟨by omega, by simp; omega, ?_, ?_⟩
        · rw [show position - start = (position - (start + 1)) + 1 by omega]
          simpa using wrong
        · intro index below'
          cases index with
          | zero => simpa using counted
          | succ index =>
              simp only [List.getD_cons_succ]
              rw [earlier index (by omega)]
              omega
      · rename_i wrong
        cases found
        refine ⟨Nat.le_refl _, by simp, by simpa using wrong, fun index below => ?_⟩
        omega

/-- No failure means the three lists are shaped. -/
public theorem triangularFailure_none {intercept : List Carrier}
    {coefficients : List (List Carrier)} {variance : List Carrier} :
    triangularFailure intercept coefficients variance = none ↔
      Shaped intercept coefficients variance := by
  unfold triangularFailure Shaped
  split
  · rename_i row ragged
    simp only [reduceCtorEq, false_iff]
    intro ⟨_, _, triangular⟩
    have none : triangularFrom 0 coefficients = none := triangularFrom_none.mpr
      (fun index row found => by rw [triangular index row found]; omega)
    rw [none] at ragged
    cases ragged
  · rename_i triangular
    have rows := triangularFrom_none.mp triangular
    split
    · rename_i lengths
      exact iff_of_true rfl ⟨lengths.1, lengths.2, fun index row found => by
        rw [rows index row found]; omega⟩
    · rename_i lengths
      simp only [reduceCtorEq, false_iff]
      exact fun shaped => lengths ⟨shaped.1, shaped.2.1⟩

/-- A failure at `k` names either the first ragged row or, at `k = |B|`, a
length of `μ` or `d`. -/
public theorem triangularFailure_some {intercept : List Carrier}
    {coefficients : List (List Carrier)} {variance : List Carrier} {position : Nat}
    (found : triangularFailure intercept coefficients variance = some position) :
    (∀ index, index < position → (coefficients.getD index []).length = index) ∧
      ((position < coefficients.length ∧ (coefficients.getD position []).length ≠ position) ∨
        (position = coefficients.length ∧
          (intercept.length ≠ position ∨ variance.length ≠ position))) := by
  unfold triangularFailure at found
  split at found
  · rename_i row ragged
    cases found
    obtain ⟨_, below, wrong, earlier⟩ := triangularFrom_some ragged
    simp only [Nat.sub_zero, Nat.zero_add] at below wrong earlier
    exact ⟨earlier, .inl ⟨below, wrong⟩⟩
  · rename_i triangular
    have rows := triangularFrom_none.mp triangular
    split at found
    · cases found
    · rename_i lengths
      cases found
      refine ⟨fun index below => ?_, .inr ⟨rfl, ?_⟩⟩
      · rw [rows index (coefficients.getD index []) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem below]; rfl)]
        omega
      · omega

/-! ### The checked network and its law -/

/-- The network the three lists form, or the failure's position. -/
@[expose] public def Network.check (intercept : List Carrier) (coefficients : List (List Carrier))
    (variance : List Carrier) (positive : ∀ value ∈ variance, lt zero value) : Nat ⊕ Network :=
  match found : triangularFailure intercept coefficients variance with
  | some position => .inl position
  | none => .inr (Network.ofLists intercept coefficients variance
      (triangularFailure_none.mp found) positive)

/-- At a failure the check names its position. -/
public theorem Network.check_failure {intercept : List Carrier} {coefficients : List (List Carrier)}
    {variance : List Carrier} (positive : ∀ value ∈ variance, lt zero value) {position : Nat}
    (found : triangularFailure intercept coefficients variance = some position) :
    Network.check intercept coefficients variance positive = .inl position := by
  unfold Network.check
  split
  · rename_i other equal
    rw [found] at equal
    cases equal
    rfl
  · rename_i equal
    rw [found] at equal
    cases equal

/-- On shaped lists the check is the network they form. -/
public theorem Network.check_shaped {intercept : List Carrier} {coefficients : List (List Carrier)}
    {variance : List Carrier} (positive : ∀ value ∈ variance, lt zero value)
    (shaped : Shaped intercept coefficients variance) :
    Network.check intercept coefficients variance positive =
      .inr (Network.ofLists intercept coefficients variance shaped positive) := by
  have none := triangularFailure_none.mpr shaped
  unfold Network.check
  split
  · rename_i other equal
    rw [none] at equal
    cases equal
  · rfl

/-- The space of a checked draw: a failure's position, or a list of reals. -/
public abbrev checkedSpace : Space (Nat ⊕ List Carrier) :=
  Space.sum (Space.discrete Nat) (Space.list borel)

/-- The law of reading three lists as a network: the point mass at `inl k` at
a failure, and the network's law in `inr` otherwise. -/
@[expose] public def checkedLaw (intercept : List Carrier) (coefficients : List (List Carrier))
    (variance : List Carrier) (positive : ∀ value ∈ variance, lt zero value) :
    Measure checkedSpace :=
  match Network.check intercept coefficients variance positive with
  | .inl position => Measure.dirac checkedSpace (.inl position)
  | .inr network => network.law.map Sum.inr (MeasurableMap.inr _ _)

/-- At a failure the checked law is the point mass at its position. -/
public theorem checkedLaw_failure {intercept : List Carrier} {coefficients : List (List Carrier)}
    {variance : List Carrier} (positive : ∀ value ∈ variance, lt zero value) {position : Nat}
    (found : triangularFailure intercept coefficients variance = some position) :
    checkedLaw intercept coefficients variance positive =
      Measure.dirac checkedSpace (.inl position) := by
  unfold checkedLaw Network.check
  split
  · rename_i checked
    split at checked
    · rename_i other
      rw [found] at other
      cases other
      cases checked
      rfl
    · cases checked
  · rename_i checked
    split at checked
    · cases checked
    · rename_i none
      rw [found] at none
      cases none

/-- On shaped lists the checked law is the network's law, in `inr`. -/
public theorem checkedLaw_shaped {intercept : List Carrier} {coefficients : List (List Carrier)}
    {variance : List Carrier} (positive : ∀ value ∈ variance, lt zero value)
    (shaped : Shaped intercept coefficients variance) :
    checkedLaw intercept coefficients variance positive =
      (Network.ofLists intercept coefficients variance shaped positive).law.map Sum.inr
        (MeasurableMap.inr _ _) := by
  have none := triangularFailure_none.mpr shaped
  unfold checkedLaw Network.check
  split
  · rename_i checked
    split at checked
    · rename_i some
      rw [none] at some
      cases some
    · cases checked
  · rename_i checked
    split at checked
    · cases checked
    · cases checked
      rfl

/-- Every checked law is a probability measure. -/
public theorem checkedLaw_isProbability (intercept : List Carrier)
    (coefficients : List (List Carrier)) (variance : List Carrier)
    (positive : ∀ value ∈ variance, lt zero value) :
    Measure.IsProbability (checkedLaw intercept coefficients variance positive) := by
  unfold checkedLaw
  split
  · exact Measure.IsProbability.dirac _ _
  · exact Measure.IsProbability.map (Network.law_isProbability _) _ (MeasurableMap.inr _ _)


/-! ### The checked density -/

/-- The density of a checked draw: one at the failure's position, and the
network's density on a draw from shaped lists. -/
@[expose] public def checkedDensity (intercept : List Carrier) (coefficients : List (List Carrier))
    (variance : List Carrier) (positive : ∀ value ∈ variance, lt zero value) :
    Nat ⊕ List Carrier → ENNReal :=
  match Network.check intercept coefficients variance positive with
  | .inl position =>
      Sum.elim (fun current => if current = position then ENNReal.one else ENNReal.zero)
        (fun _ => ENNReal.zero)
  | .inr network =>
      Sum.elim (fun _ => ENNReal.zero) (fun values => ENNReal.finite (network.density values))

public theorem checkedDensity_measurable (intercept : List Carrier)
    (coefficients : List (List Carrier)) (variance : List Carrier)
    (positive : ∀ value ∈ variance, lt zero value) :
    ENNRealMeasurable checkedSpace (checkedDensity intercept coefficients variance positive) := by
  unfold checkedDensity
  apply ENNRealMeasurable.of_measurableMap
  split
  · exact MeasurableMap.sum_elim (fun _ => True.intro) (MeasurableMap.constant _ _ _)
  · exact MeasurableMap.sum_elim (fun _ => True.intro) (Network.density_measurable _).measurableMap

/-- The reference of checked draws: a counting measure on failure positions,
and the list volume of every length on draws. -/
@[expose] public def checkedReference (counting : Measure (Space.discrete Nat)) :
    Measure checkedSpace :=
  Measure.add (counting.map Sum.inl (MeasurableMap.inl _ _))
    ((Measure.sum listVolume).map Sum.inr (MeasurableMap.inr _ _))

/-- Integrating against the checked reference splits into the failure
positions and the draws of every length. -/
private theorem lintegral_checkedReference (counting : Measure (Space.discrete Nat))
    {integrand : Nat ⊕ List Carrier → ENNReal} (measurable : ENNRealMeasurable checkedSpace integrand) :
    lintegral (checkedReference counting) integrand =
      ENNReal.add (lintegral counting fun position => integrand (.inl position))
        (ENNReal.tsum fun count => lintegral (listVolume count) fun values => integrand (.inr values)) := by
  unfold checkedReference
  rw [lintegral_add_measure, lintegral_map _ _ (MeasurableMap.inl _ _) measurable,
    lintegral_map _ _ (MeasurableMap.inr _ _) measurable, lintegral_sum_measure]

/-- The checked law has the checked density against the checked reference,
for any counting measure that gives each position mass one. -/
public theorem checkedLaw_eq_withDensity (counting : Measure (Space.discrete Nat))
    (singleton : ∀ position, counting (fun value => value = position) = ENNReal.one)
    (intercept : List Carrier) (coefficients : List (List Carrier)) (variance : List Carrier)
    (positive : ∀ value ∈ variance, lt zero value) :
    checkedLaw intercept coefficients variance positive =
      (checkedReference counting).withDensity (checkedDensity intercept coefficients variance positive) := by
  have densityMeasurable := checkedDensity_measurable intercept coefficients variance positive
  refine (Measure.eq_iff_lintegral _ _).mpr fun integrand measurable => ?_
  rw [lintegral_withDensity _ densityMeasurable measurable,
    lintegral_checkedReference counting (ENNRealMeasurable.mul densityMeasurable measurable)]
  unfold checkedLaw checkedDensity
  rcases checked : Network.check intercept coefficients variance positive with position | network
  · dsimp only
    rw [lintegral_dirac _ _ measurable]
    simp only [Sum.elim_inl, Sum.elim_inr, ENNReal.zero_mul, lintegral_zero, ENNReal.tsum_zero,
      ENNReal.add_zero]
    have indicator : (fun current => ENNReal.mul
        (if current = position then ENNReal.one else ENNReal.zero) (integrand (.inl current))) =
        ennrealIndicator (fun current => current = position) (fun _ => integrand (.inl position)) := by
      funext current
      unfold ennrealIndicator ennrealPiecewise
      by_cases same : current = position
      · subst same
        simp only [ite_true, ENNReal.one_mul]
      · simp only [same, ite_false, ENNReal.zero_mul]
    rw [indicator, lintegral_indicator _ _ True.intro, lintegral_const,
      Measure.restrict_apply _ _ True.intro, Set.inter_univ_left, singleton, ENNReal.mul_one]
  · dsimp only
    simp only [Sum.elim_inl, Sum.elim_inr, ENNReal.zero_mul, lintegral_zero, ENNReal.zero_add]
    rw [lintegral_map _ _ (MeasurableMap.inr _ _) measurable, network.law_eq_withDensity,
      lintegral_withDensity _ network.density_measurable
        (ENNRealMeasurable.comp measurable (MeasurableMap.inr _ _))]
    refine (ENNReal.tsum_eq_of_at_most_one_nonzero (fun count => lintegral (listVolume count)
      fun values => ENNReal.mul (ENNReal.finite (network.density values)) (integrand (.inr values)))
      network.length fun count other => ?_).symm
    refine (lintegral_congr_ae (Measure.NullSet.mono (listVolume_length_null count) ?_)).trans
      (lintegral_zero _)
    intro values different counted
    apply different
    show ENNReal.mul (ENNReal.finite (network.density values)) (integrand (.inr values)) = ENNReal.zero
    unfold Network.density
    rw [ite_eq_right (fun equal => other (counted.symm.trans equal)),
      show ENNReal.finite NNReal.zero = ENNReal.zero from rfl, ENNReal.zero_mul]

end

end Problib.Analysis.Gaussian
