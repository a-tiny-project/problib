module

public import Problib.Inference.MetropolisHastings.Support
public import Problib.Measure.Kernel.Iteration.Recurrence

set_option autoImplicit false

/-! Harris recurrence from dominated moves.

An invariant, irreducible Markov step hits every charged event from almost
every start (`invariant_hits_almost_everywhere`). Dominated moves upgrade that
to every start (`harris_of_dominated_moves`). Outside the event, the hitting
probability `h` of a state satisfies `h = a + b·h`, where `b` is the holding
probability and `a = 1 - b` is the accepted mass. The accepted part integrates
`h` as if it were one, because it charges no target-null set and `h = 1` off a
target-null set. So `h = 1` when `b < 1`. When `b = 1` the state is absorbing,
and irreducibility forbids an absorbing state outside a charged event.

Recurrence on a region also extends to every start that enters the region
almost surely (`harris_of_entrance`), through the strong Markov bound
`lintegral_hitKernel_le`. A Metropolis step with a proposal density, a
nonnegative weight and a finite irreducible target is Harris recurrent
(`metropolis_harris`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure Problib.Measure.Kernel

universe u

variable {α : Type u} {space : Space α}

public section

/-- A probability `h` with `h = a + b·h`, where `a + b = 1` and `b ≠ 1`, is one. -/
private theorem affine_fixed_one {accepted holding hit : ENNReal}
    (total : ENNReal.add accepted holding = ENNReal.one)
    (fixed : hit = ENNReal.add accepted (ENNReal.mul holding hit))
    (bounded : ENNReal.le hit ENNReal.one) (moving : holding ≠ ENNReal.one) :
    hit = ENNReal.one := by
  have oneFinite : ENNReal.Finite ENNReal.one := True.intro
  have le_of_add_left : ∀ {left right : ENNReal}, ENNReal.add left right = ENNReal.one →
      ENNReal.le left ENNReal.one := by
    intro left right sum
    have shifted := ENNReal.add_le_add_left (ENNReal.zero_le right) left
    rwa [ENNReal.add_zero, sum] at shifted
  have holdingBounded : ENNReal.le holding ENNReal.one :=
    le_of_add_left (by rw [ENNReal.add_comm]; exact total)
  have acceptedFinite := ENNReal.finite_of_le (le_of_add_left total) oneFinite
  have holdingFinite := ENNReal.finite_of_le holdingBounded oneFinite
  have hitFinite := ENNReal.finite_of_le bounded oneFinite
  let missing := ENNReal.sub ENNReal.one hit
  have split : ENNReal.add missing hit = ENNReal.one := ENNReal.sub_add_cancel bounded
  have missingFinite := ENNReal.finite_of_le (le_of_add_left split) oneFinite
  -- `a + b = 1 = s + h = a + (s + b·h)`, so `b = s + b·h`.
  have holdingSplit : holding = ENNReal.add missing (ENNReal.mul holding hit) := by
    apply ENNReal.add_left_cancel_of_finite acceptedFinite
    rw [total, ← split]
    conv => lhs; rw [fixed]
    rw [ENNReal.add_left_comm]
  -- `b = b·(s + h) = b·s + b·h`, so `s = b·s`.
  have missingFixed : missing = ENNReal.mul holding missing := by
    apply ENNReal.add_right_cancel_of_finite
      (ENNReal.mul_finite holdingFinite hitFinite)
    rw [← holdingSplit, ← ENNReal.mul_add, split, ENNReal.mul_one]
  -- `s = (1 - b)·s + b·s`, so `(1 - b)·s = 0`.
  have remainder : ENNReal.mul (ENNReal.sub ENNReal.one holding) missing = ENNReal.zero := by
    apply ENNReal.add_right_cancel_of_finite
      (ENNReal.mul_finite holdingFinite missingFinite)
    rw [ENNReal.zero_add, ENNReal.mul_comm (ENNReal.sub ENNReal.one holding),
      ENNReal.mul_comm holding, ← ENNReal.mul_add, ENNReal.sub_add_cancel holdingBounded,
      ENNReal.mul_one, ENNReal.mul_comm]
    exact missingFixed
  rcases ENNReal.mul_eq_zero_iff.mp remainder with zeroGap | zeroMissing
  · have restored := ENNReal.sub_add_cancel holdingBounded
    rw [zeroGap, ENNReal.zero_add] at restored
    exact False.elim (moving restored)
  · have restored := split
    rw [zeroMissing, ENNReal.zero_add] at restored
    exact restored

/-- An invariant, irreducible Markov step with dominated moves is Harris
recurrent: it hits every charged event from every start, not only from almost
every start. -/
theorem harris_of_dominated_moves {kernel : Kernel space space} {reference : Measure space}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (finite : Measure.IsFinite reference)
    (invariant : KernelInvariant reference kernel)
    (irreducible : MeasureIrreducible kernel reference)
    (dominated : DominatedMoves kernel reference) :
    HarrisRecurrent kernel reference := by
  intro event measurable positive input
  rcases dominated with ⟨accepted, holding, _, _, decomposition, acceptedDominated⟩
  by_cases inside : event input
  · exact hitsAlmostSurely_of_mem kernel event input measurable inside
  apply (hitsAlmostSurely_iff kernel event input measurable).mpr
  let hit : α → ENNReal := fun state => hitKernel kernel event measurable state Set.univ
  have hitMeasurable : ENNRealMeasurable space hit :=
    (hitKernel kernel event measurable).measurable space.univ
  have almostSure : reference.AEEq hit (fun _ => ENNReal.one) :=
    (invariant_hits_almost_everywhere markov finite invariant irreducible measurable
      positive).mono (fun state hits =>
        (hitsAlmostSurely_iff kernel event state measurable).mp hits)
  -- One step from outside the event.
  have firstStep : hit input = lintegral (kernel input) hit := by
    change hitKernel kernel event measurable input Set.univ = _
    conv => lhs; rw [hitKernel_unfold]
    rw [Kernel.add_apply, Measure.add_apply_measurable _ _ space.univ, exitInside,
      piecewise_apply_of_not_mem _ _ _ _ _ inside, Kernel.zero_apply, Measure.zero_apply,
      ENNReal.zero_add, Kernel.comp_apply, continueOutside,
      piecewise_apply_of_not_mem _ _ _ _ _ inside, Measure.bind_apply _ _ space.univ]
  have acceptedIntegral : lintegral (accepted input) hit = accepted input Set.univ := by
    rw [lintegral_congr_ae
      (Measure.AbsolutelyContinuous.aeEq (acceptedDominated input) almostSure), lintegral_const,
      ENNReal.one_mul]
  have fixed : hit input =
      ENNReal.add (accepted input Set.univ) (ENNReal.mul (holding input) (hit input)) := by
    conv => lhs; rw [firstStep]
    rw [decomposition input, lintegral_add_measure, lintegral_smul_measure,
      lintegral_dirac _ _ hitMeasurable, acceptedIntegral]
  have total : ENNReal.add (accepted input Set.univ) (holding input) = ENNReal.one := by
    have mass := (markov input).univ_eq_one
    rw [decomposition input, Measure.add_apply_measurable _ _ space.univ,
      Measure.smul_apply_measurable _ _ space.univ, Measure.dirac_apply_univ,
      ENNReal.mul_one] at mass
    exact mass
  have bounded : ENNReal.le (hit input) ENNReal.one :=
    hit_mass_le_one kernel event measurable markov input
  by_cases moving : holding input = ENNReal.one
  · -- A state that always holds is absorbing, and irreducibility forbids it.
    apply False.elim
    have acceptedNull : accepted input Set.univ = ENNReal.zero := by
      apply ENNReal.add_right_cancel_of_finite (factor := ENNReal.one) True.intro
      rw [← moving, total, ENNReal.zero_add, moving]
    have absorbing : kernel input = Measure.dirac space input := by
      apply Measure.ext
      intro set setMeasurable
      have acceptedSet : accepted input set = ENNReal.zero :=
        ENNReal.eq_zero_of_le_zero
          (acceptedNull ▸ (accepted input).mono (Set.subset_univ set))
      rw [decomposition input, Measure.add_apply_measurable _ _ setMeasurable,
        Measure.smul_apply_measurable _ _ setMeasurable, acceptedSet, moving,
        ENNReal.zero_add, ENNReal.one_mul]
    have stays : ∀ count, iterate kernel count input = Measure.dirac space input := by
      intro count
      induction count with
      | zero => rw [iterate_zero, Kernel.deterministic_apply]
      | succ count induction =>
          rw [iterate_succ, Kernel.comp_apply, absorbing, Measure.dirac_bind, induction]
    rcases irreducible.reaches event measurable positive input with ⟨count, reached⟩
    rw [stays, Measure.dirac_apply_of_not_mem _ _ measurable inside] at reached
    exact ENNReal.zero_lt_iff_ne_zero.mp reached rfl
  · exact affine_fixed_one total fixed bounded moving


/-- A chain that hits every charged event from every state of a region, and
enters the region almost surely from every state, is Harris recurrent. -/
theorem harris_of_entrance {kernel : Kernel space space} {reference : Measure space}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (region : Set α) (regionMeasurable : space.Measurable region)
    (harrisOnRegion : ∀ event, space.Measurable event →
      ENNReal.lt ENNReal.zero (reference event) →
        ∀ input, region input → HitsAlmostSurely kernel event input)
    (entrance : ∀ input, HitsAlmostSurely kernel region input) :
    HarrisRecurrent kernel reference := by
  intro event measurable positive input
  apply (hitsAlmostSurely_iff kernel event input measurable).mpr
  have entered : hitKernel kernel region regionMeasurable input Set.univ = ENNReal.one :=
    (hitsAlmostSurely_iff kernel region input regionMeasurable).mp (entrance input)
  have inside : hitKernel kernel region regionMeasurable input region = ENNReal.one := by
    have split := (hitKernel kernel region regionMeasurable input).union_disjoint
      regionMeasurable (space.complement regionMeasurable)
      (fun _ member outside => outside member)
    have cover : Set.union region (Set.complement region) = Set.univ :=
      Set.ext fun state => ⟨fun _ => trivial, fun _ => Classical.em (region state)⟩
    rw [cover, entered, hitKernel_concentrated, ENNReal.add_zero] at split
    exact split.symm
  have lower : ENNReal.le (hitKernel kernel region regionMeasurable input region)
      (lintegral (hitKernel kernel region regionMeasurable input)
        (fun state => hitKernel kernel event measurable state Set.univ)) := by
    rw [apply_eq_lintegral_indicator _ regionMeasurable]
    apply lintegral_mono
    intro state
    classical
    by_cases member : region state
    · simp only [ennrealIndicator, ennrealPiecewise, member, ite_true]
      rw [(hitsAlmostSurely_iff kernel event state measurable).mp
        (harrisOnRegion event measurable positive state member)]
      exact ENNReal.le_refl _
    · simp only [ennrealIndicator, ennrealPiecewise, member, ite_false]
      exact ENNReal.zero_le _
  apply ENNReal.le_antisymm (hit_mass_le_one kernel event measurable markov input)
  rw [← inside]
  exact ENNReal.le_trans lower
    (lintegral_hitKernel_le kernel markov region event regionMeasurable measurable input)

/-- A Metropolis step with a reversible proposal that has a density, a
nonnegative measurable weight, and a finite weighted target it reaches from
every state is Harris recurrent for that target. -/
theorem metropolis_harris (reference : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    (reversible : DetailedBalance reference proposal proposalFinite)
    (proposalDensity : α → α → ENNReal)
    (proposalDensityMeasurable : ∀ input, ENNRealMeasurable space (proposalDensity input))
    (proposalRepresents : ∀ input,
      proposal input = reference.withDensity (proposalDensity input))
    {weight : α → Measure.Real.Carrier} (weightMeasurable : MeasurableMap space Measure.Real.borel weight)
    (nonnegative : ∀ state,
      Construction.Dedekind.le Construction.Dedekind.zero (weight state))
    (finite : Measure.IsFinite
      (reference.withDensity fun state => ENNReal.ofReal (weight state)))
    (irreducible : MeasureIrreducible
      (mhKernel proposal proposalFinite (metropolisAccept weight)
        (metropolisAccept_measurable weightMeasurable))
      (reference.withDensity fun state => ENNReal.ofReal (weight state))) :
    HarrisRecurrent
      (mhKernel proposal proposalFinite (metropolisAccept weight)
        (metropolisAccept_measurable weightMeasurable))
      (reference.withDensity fun state => ENNReal.ofReal (weight state)) :=
  harris_of_dominated_moves
    (mhKernel_markov proposalFinite proposalMarkov _ (metropolisAccept_le_one weight))
    finite (metropolis_invariant reference proposalFinite proposalMarkov reversible weightMeasurable)
    irreducible
    (metropolis_dominated proposal proposalFinite proposalMarkov reference proposalDensity
      proposalDensityMeasurable proposalRepresents weightMeasurable nonnegative)

end

end Problib.Inference
