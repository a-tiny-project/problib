module

public import Problib.Measure.Kernel.Iteration.Termination
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.Kernel.Piecewise
public import Problib.Measure.Integral.Lebesgue.Infimum
import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-- Continue until the chain enters the region. -/
@[expose] public noncomputable def continueOutside (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region) : Kernel space space :=
  piecewise region measurable (Kernel.zero space space) kernel

/-- Return the state on its first visit to the region. -/
@[expose] public noncomputable def exitInside (region : Set α)
    (measurable : space.Measurable region) : Kernel space space :=
  piecewise region measurable
    (Kernel.deterministic (fun value => value) (MeasurableMap.identity space))
    (Kernel.zero space space)

@[expose] public noncomputable def stayOutside (region : Set α)
    (measurable : space.Measurable region) : Kernel space space :=
  piecewise region measurable (Kernel.zero space space)
    (Kernel.deterministic (fun value => value) (MeasurableMap.identity space))

@[expose] public noncomputable def hitKernel (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region) : Kernel space space :=
  loop (continueOutside kernel region measurable) (exitInside region measurable)

@[expose] public noncomputable def survival (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region)
    (count : Nat) (input : α) : ENNReal :=
  iterate (continueOutside kernel region measurable) count input Set.univ

@[expose] public def HitsAlmostSurely (kernel : Kernel space space)
    (region : Set α) (input : α) : Prop :=
  ∃ measurable : space.Measurable region,
    hitKernel kernel region measurable input Set.univ = ENNReal.one

public theorem exitInside_add_stayOutside (region : Set α)
    (measurable : space.Measurable region) :
    Kernel.add (exitInside region measurable) (stayOutside region measurable) =
      Kernel.deterministic (fun value => value) (MeasurableMap.identity space) := by
  apply Kernel.ext
  intro input
  by_cases member : region input
  · simp only [exitInside, stayOutside,
      piecewise_apply_of_mem _ _ _ _ _ member, Kernel.add_apply,
      Kernel.zero_apply, Measure.add_zero]
  · simp only [exitInside, stayOutside,
      piecewise_apply_of_not_mem _ _ _ _ _ member, Kernel.add_apply,
      Kernel.zero_apply, Measure.zero_add]

public theorem stayOutside_comp (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region) :
    (stayOutside region measurable).comp kernel =
      continueOutside kernel region measurable := by
  apply Kernel.ext
  intro input
  by_cases member : region input
  · rw [comp_apply, stayOutside, piecewise_apply_of_mem _ _ _ _ _ member,
      Kernel.zero_apply, Measure.zero_bind, continueOutside,
      piecewise_apply_of_mem _ _ _ _ _ member, Kernel.zero_apply]
  · rw [comp_apply, stayOutside, piecewise_apply_of_not_mem _ _ _ _ _ member,
      Kernel.deterministic_apply, Measure.dirac_bind, continueOutside,
      piecewise_apply_of_not_mem _ _ _ _ _ member]

public theorem continueOutside_congr {left right : Kernel space space}
    (region : Set α) (measurable : space.Measurable region)
    (agree : ∀ input, ¬ region input → left input = right input) :
    continueOutside left region measurable = continueOutside right region measurable := by
  apply Kernel.ext
  intro input
  by_cases member : region input
  · simp only [continueOutside, piecewise_apply_of_mem _ _ _ _ _ member]
  · simpa only [continueOutside, piecewise_apply_of_not_mem _ _ _ _ _ member]
      using agree input member

public theorem hitting_conservative (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    ENNReal.add (continueOutside kernel region measurable input Set.univ)
      (exitInside region measurable input Set.univ) = ENNReal.one := by
  by_cases member : region input
  · simp only [continueOutside, exitInside,
      piecewise_apply_of_mem _ _ _ _ _ member, Kernel.zero_apply,
      Measure.zero_apply, Kernel.deterministic_apply,
      Measure.dirac_apply_univ, ENNReal.zero_add]
  · simp only [continueOutside, exitInside,
      piecewise_apply_of_not_mem _ _ _ _ _ member, Kernel.zero_apply,
      Measure.zero_apply, ENNReal.add_zero]
    exact (markov input).univ_eq_one

public theorem hit_mass_add_survival (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    ENNReal.add (hitKernel kernel region measurable input Set.univ)
      (ENNReal.iInf (fun count => survival kernel region measurable count input)) =
      ENNReal.one := by
  exact loop_mass_add_iInf_eq_one _ _
    (hitting_conservative kernel region measurable markov) input

public theorem hit_mass_eq_one_iff_survival_vanishes
    (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    hitKernel kernel region measurable input Set.univ = ENNReal.one ↔
      ENNReal.iInf (fun count => survival kernel region measurable count input) =
        ENNReal.zero := by
  exact loop_mass_one_iff _ _
    (hitting_conservative kernel region measurable markov) input

public theorem hitsAlmostSurely_iff (kernel : Kernel space space) (region : Set α)
    (input : α) (measurable : space.Measurable region) :
    HitsAlmostSurely kernel region input ↔
      hitKernel kernel region measurable input Set.univ = ENNReal.one := by
  constructor
  · rintro ⟨other, holds⟩
    have same : other = measurable := Subsingleton.elim _ _
    simpa only [same] using holds
  · intro holds
    exact ⟨measurable, holds⟩

public theorem hitsAlmostSurely_of_mem (kernel : Kernel space space)
    (region : Set α) (input : α) (measurable : space.Measurable region)
    (member : region input) : HitsAlmostSurely kernel region input := by
  apply (hitsAlmostSurely_iff kernel region input measurable).mpr
  rw [hitKernel, loop_unfold, Kernel.add_apply,
    Measure.add_apply_measurable _ _ space.univ, exitInside,
    piecewise_apply_of_mem _ _ _ _ _ member,
    Kernel.deterministic_apply, Measure.dirac_apply_univ]
  have continuationZero :
      continueOutside kernel region measurable input = Measure.zero space := by
    rw [continueOutside, piecewise_apply_of_mem _ _ _ _ _ member,
      Kernel.zero_apply]
  rw [Kernel.comp_apply, continuationZero, Measure.zero_bind,
    Measure.zero_apply, ENNReal.add_zero]

public theorem hitKernel_unfold (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region) :
    hitKernel kernel region measurable =
      Kernel.add (exitInside region measurable)
        ((continueOutside kernel region measurable).comp
          (hitKernel kernel region measurable)) := by
  exact loop_unfold _ _

public theorem hitKernel_concentrated (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region) (input : α) :
    hitKernel kernel region measurable input (Set.complement region) = ENNReal.zero := by
  have complementMeasurable := space.complement measurable
  have exitZero : ∀ state, exitInside region measurable state
      (Set.complement region) = ENNReal.zero := by
    intro state
    by_cases member : region state
    · rw [exitInside, piecewise_apply_of_mem _ _ _ _ _ member,
        Kernel.deterministic_apply]
      exact Measure.dirac_apply_of_not_mem space state
        complementMeasurable (fun outside => outside member)
    · rw [exitInside, piecewise_apply_of_not_mem _ _ _ _ _ member,
        Kernel.zero_apply, Measure.zero_apply]
  have termZero : ∀ count state,
      ((iterate (continueOutside kernel region measurable) count).comp
        (exitInside region measurable)) state (Set.complement region) =
          ENNReal.zero := by
    intro count state
    rw [comp_apply_measurable _ _ _ complementMeasurable]
    exact (lintegral_congr _ exitZero).trans (lintegral_zero _)
  have prefixZero : ∀ count state,
      prefixApproximant (continueOutside kernel region measurable)
        (exitInside region measurable) count state (Set.complement region) =
          ENNReal.zero := by
    intro count
    induction count with
    | zero =>
        intro state
        rw [prefixApproximant_zero, Kernel.zero_apply, Measure.zero_apply]
    | succ count induction =>
        intro state
        rw [prefixApproximant_succ, Kernel.add_apply,
          Measure.add_apply_measurable _ _ complementMeasurable,
          induction state, termZero count state, ENNReal.zero_add]
  rw [hitKernel, loop_eq_iSup_prefixApproximant _ _ input complementMeasurable]
  apply ENNReal.le_antisymm
  · apply ENNReal.iSup_le
    intro count
    rw [prefixZero count input]
    exact ENNReal.le_refl _
  · exact ENNReal.zero_le _

public theorem survival_succ (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region) (count : Nat) (input : α) :
    survival kernel region measurable (count + 1) input =
      lintegral (continueOutside kernel region measurable input)
        (survival kernel region measurable count) := by
  rw [survival, iterate_succ, comp_apply_measurable _ _ _ space.univ]
  rfl

public theorem entrance_peel (kernel : Kernel space space) (region : Set α)
    (measurable : space.Measurable region) (horizon count : Nat) :
    (iterate (continueOutside kernel region measurable) horizon).comp
        (iterate kernel (count + 1)) =
      Kernel.add
        (((iterate (continueOutside kernel region measurable) horizon).comp
          (exitInside region measurable)).comp (iterate kernel (count + 1)))
        ((iterate (continueOutside kernel region measurable) (horizon + 1)).comp
          (iterate kernel count)) := by
  let T := continueOutside kernel region measurable
  let E := exitInside region measurable
  let F := stayOutside region measurable
  have split := exitInside_add_stayOutside (space := space) region measurable
  have continuation := stayOutside_comp kernel region measurable
  have identityComp : (Kernel.add E F).comp (iterate kernel (count + 1)) =
      iterate kernel (count + 1) := by
    rw [split]
    apply Kernel.ext
    intro state
    exact deterministic_comp_apply _ _ _ state
  have tail : F.comp (iterate kernel (count + 1)) =
      T.comp (iterate kernel count) := by
    rw [iterate_succ, ← comp_assoc, continuation]
  calc
    (iterate T horizon).comp (iterate kernel (count + 1)) =
        (iterate T horizon).comp
          ((Kernel.add E F).comp (iterate kernel (count + 1))) :=
      congrArg ((iterate T horizon).comp) identityComp.symm
    _ = (iterate T horizon).comp
          (Kernel.add (E.comp (iterate kernel (count + 1)))
            (F.comp (iterate kernel (count + 1)))) := by
      rw [add_comp_distrib]
    _ = Kernel.add
          ((iterate T horizon).comp (E.comp (iterate kernel (count + 1))))
          ((iterate T horizon).comp (F.comp (iterate kernel (count + 1)))) := by
      rw [comp_add_distrib]
    _ = Kernel.add
          (((iterate T horizon).comp E).comp (iterate kernel (count + 1)))
          ((iterate T (horizon + 1)).comp (iterate kernel count)) := by
      rw [← comp_assoc, tail, ← comp_assoc]
      exact congrArg
        (Kernel.add (((iterate T horizon).comp E).comp
          (iterate kernel (count + 1))))
        (congrArg (fun current => current.comp (iterate kernel count))
          (iterate_succ_right T horizon).symm)

private theorem continueOutside_le (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region) :
    Kernel.le (continueOutside kernel region measurable) kernel := by
  intro state event eventMeasurable
  by_cases member : region state
  · rw [continueOutside, piecewise_apply_of_mem _ _ _ _ _ member,
      Kernel.zero_apply, Measure.zero_apply]
    exact ENNReal.zero_le _
  · rw [continueOutside, piecewise_apply_of_not_mem _ _ _ _ _ member]
    exact ENNReal.le_refl _

private theorem continueOutside_iterate_le (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region)
    (count : Nat) :
    Kernel.le (iterate (continueOutside kernel region measurable) count)
      (iterate kernel count) := by
  let T := continueOutside kernel region measurable
  have Tle := continueOutside_le kernel region measurable
  induction count with
  | zero => exact Kernel.le_refl _
  | succ count induction =>
      rw [iterate_succ, iterate_succ]
      exact Kernel.le_trans
        (Kernel.comp_le_comp_right T induction)
        (Kernel.comp_le_comp_left Tle (iterate kernel count))

private theorem exitInside_comp_mass (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region)
    (count : Nat) (state : α) :
    ((iterate (continueOutside kernel region measurable) count).comp
      (exitInside region measurable)) state Set.univ =
        iterate (continueOutside kernel region measurable) count state region := by
  let T := continueOutside kernel region measurable
  have integrand : (fun value => exitInside region measurable value Set.univ) =
      ennrealIndicator region (fun _ => ENNReal.one) := by
    funext value
    by_cases member : region value
    · simp only [exitInside, piecewise_apply_of_mem _ _ _ _ _ member,
        Kernel.deterministic_apply, Measure.dirac_apply_univ,
        ennrealIndicator, ennrealPiecewise, if_pos member]
    · simp only [exitInside, piecewise_apply_of_not_mem _ _ _ _ _ member,
        Kernel.zero_apply, Measure.zero_apply,
        ennrealIndicator, ennrealPiecewise, if_neg member]
  rw [comp_apply_measurable _ _ _ space.univ, integrand]
  exact (apply_eq_lintegral_indicator _ measurable).symm

private theorem positive_of_positive_le {left right : ENNReal}
    (positive : ENNReal.lt ENNReal.zero left)
    (included : ENNReal.le left right) : ENNReal.lt ENNReal.zero right :=
  ⟨ENNReal.le_trans positive.1 included,
    fun reverse => positive.2 (ENNReal.le_trans included reverse)⟩

public theorem hit_positive_iff_reaches (kernel : Kernel space space)
    (region : Set α) (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    ENNReal.lt ENNReal.zero (hitKernel kernel region measurable input Set.univ) ↔
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region) := by
  let T := continueOutside kernel region measurable
  let E := exitInside region measurable
  let H := hitKernel kernel region measurable
  have termBound : ∀ count state,
      ENNReal.le (((iterate T count).comp E) state Set.univ)
        (iterate kernel count state region) := by
    intro count state
    rw [exitInside_comp_mass]
    exact continueOutside_iterate_le kernel region measurable
      count state region measurable
  have hitBound : ∀ count state,
      ENNReal.le (iterate kernel count state region) (H state Set.univ) := by
    intro count
    induction count with
    | zero =>
        intro state
        rw [iterate_zero, Kernel.deterministic_apply,
          Measure.dirac_apply space state measurable]
        by_cases member : region state
        · rw [if_pos member]
          rw [(hitsAlmostSurely_iff kernel region state measurable).mp
            (hitsAlmostSurely_of_mem kernel region state measurable member)]
          exact ENNReal.le_refl _
        · rw [if_neg member]
          exact ENNReal.zero_le _
    | succ count induction =>
        intro state
        by_cases member : region state
        · exact ENNReal.le_trans
            ((iterate_isProbability kernel markov (count + 1) state).apply_le_one region)
            (by
              rw [(hitsAlmostSurely_iff kernel region state measurable).mp
                (hitsAlmostSurely_of_mem kernel region state measurable member)]
              exact ENNReal.le_refl _)
        · have unfoldAt := congrArg
            (fun current : Kernel space space => current state Set.univ)
            (hitKernel_unfold kernel region measurable)
          rw [Kernel.add_apply,
            Measure.add_apply_measurable _ _ space.univ] at unfoldAt
          have termLe : ENNReal.le
              ((T.comp H) state Set.univ) (H state Set.univ) := by
            have included := ENNReal.add_le_add_right
              (ENNReal.zero_le (E state Set.univ))
              ((T.comp H) state Set.univ)
            rw [ENNReal.zero_add, ← unfoldAt] at included
            exact included
          rw [iterate_succ, comp_apply_measurable _ _ _ measurable]
          have integrated := lintegral_mono (kernel state)
            (fun successor => induction successor)
          have same : T state = kernel state := by
            exact piecewise_apply_of_not_mem _ _ _ _ _ member
          have upperEq : lintegral (kernel state)
              (fun successor => H successor Set.univ) =
              (T.comp H) state Set.univ := by
            rw [← same, comp_apply_measurable T H state space.univ]
          rw [upperEq] at integrated
          exact ENNReal.le_trans integrated termLe
  constructor
  · intro hitPositive
    have sumPositive : ENNReal.lt ENNReal.zero
        (ENNReal.tsum (fun count => ((iterate T count).comp E) input Set.univ)) := by
      simpa only [H, hitKernel, loop_apply, Measure.sum_apply _ space.univ]
        using hitPositive
    have somePositive : ∃ count,
        ENNReal.lt ENNReal.zero (((iterate T count).comp E) input Set.univ) := by
      apply Classical.byContradiction
      intro absent
      have allZero : ∀ count,
          ((iterate T count).comp E) input Set.univ = ENNReal.zero := by
        intro count
        exact Classical.byContradiction (fun nonzero =>
          absent ⟨count, ENNReal.zero_lt_iff_ne_zero.mpr nonzero⟩)
      have zero := ENNReal.tsum_eq_zero_iff.mpr allZero
      exact (ENNReal.zero_lt_iff_ne_zero.mp sumPositive) zero
    rcases somePositive with ⟨count, positive⟩
    exact ⟨count, positive_of_positive_le positive (termBound count input)⟩
  · rintro ⟨count, positive⟩
    exact positive_of_positive_le positive (hitBound count input)

end Problib.Measure.Kernel
