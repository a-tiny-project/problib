module

public import Foundations.Measure.Kernel.Iteration.Basic
public import Foundations.Real.Extended.Infimum
import Foundations.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

namespace Foundations.Measure.Kernel
open Foundations.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- The one-step recurrence for output plus continuing mass. -/
public theorem prefix_mass_recurrence (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) (input : alpha) :
    ENNReal.add (prefixApproximant step exit (count + 1) input Set.univ)
        (iterate step (count + 1) input Set.univ) =
      ENNReal.add (exit input Set.univ)
        (lintegral (step input) (fun value =>
          ENNReal.add (prefixApproximant step exit count value Set.univ)
            (iterate step count value Set.univ))) := by
  rw [prefixApproximant_step_unfold, Kernel.add_apply,
    Measure.add_apply_measurable _ _ target.univ, iterate_succ,
    comp_apply_measurable _ _ _ target.univ,
    comp_apply_measurable _ _ _ source.univ, ENNReal.addAssoc,
    lintegral_add (step input)
      ((prefixApproximant step exit count).measurable target.univ)
      ((iterate step count).measurable source.univ)]

/-- A substochastic continuation/exit pair cannot gain mass in any finite prefix. -/
public theorem prefix_mass_le_one (step : Kernel source source)
    (exit : Kernel source target)
    (substochastic : ∀ input, ENNReal.le
      (ENNReal.add (step input Set.univ) (exit input Set.univ)) ENNReal.one)
    (count : Nat) (input : alpha) :
    ENNReal.le (ENNReal.add (prefixApproximant step exit count input Set.univ)
      (iterate step count input Set.univ)) ENNReal.one := by
  induction count generalizing input with
  | zero =>
    rw [prefixApproximant_zero, Kernel.zero_apply, Measure.zero_apply,
      iterate_zero, deterministic_apply, Measure.dirac_apply_univ, ENNReal.zeroAdd]
    exact ENNReal.leRefl _
  | succ count induction =>
    rw [prefix_mass_recurrence]
    have integralBound := lintegral_mono (step input) induction
    rw [lintegral_const, ENNReal.oneMul] at integralBound
    exact ENNReal.leTrans (ENNReal.addLeAddLeft integralBound _)
      (by rw [ENNReal.addComm]; exact substochastic input)

/-- Conservation gives exact finite-prefix mass balance. -/
public theorem prefix_mass_eq_one (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) :
    ENNReal.add (prefixApproximant step exit count input Set.univ)
      (iterate step count input Set.univ) = ENNReal.one := by
  induction count generalizing input with
  | zero =>
    rw [prefixApproximant_zero, Kernel.zero_apply, Measure.zero_apply,
      iterate_zero, deterministic_apply, Measure.dirac_apply_univ, ENNReal.zeroAdd]
  | succ count induction =>
    rw [prefix_mass_recurrence, lintegral_congr (step input) induction,
      lintegral_const, ENNReal.oneMul, ENNReal.addComm]
    exact conservative input

/-- The unbounded output of a substochastic pair has mass at most one. -/
public theorem loop_mass_le_one (step : Kernel source source)
    (exit : Kernel source target)
    (substochastic : ∀ input, ENNReal.le
      (ENNReal.add (step input Set.univ) (exit input Set.univ)) ENNReal.one)
    (input : alpha) : ENNReal.le (loop step exit input Set.univ) ENNReal.one := by
  rw [loop_eq_iSup_prefixApproximant step exit input target.univ]
  apply ENNReal.iSupLe
  intro count
  have included := ENNReal.addLeAddLeft (ENNReal.zeroLe
    (iterate step count input Set.univ)) (prefixApproximant step exit count input Set.univ)
  rw [ENNReal.addZero] at included
  exact ENNReal.leTrans included (prefix_mass_le_one step exit substochastic count input)

public theorem loop_isFinite (step : Kernel source source)
    (exit : Kernel source target)
    (substochastic : ∀ input, ENNReal.le
      (ENNReal.add (step input Set.univ) (exit input Set.univ)) ENNReal.one) :
    IsFinite (loop step exit) :=
  ⟨⟨ENNReal.one, True.intro, loop_mass_le_one step exit substochastic⟩⟩

/-- A substochastic pair supplies uniform finiteness certificates for both inputs. -/
public theorem substochastic_isFinite (step : Kernel source source)
    (exit : Kernel source target)
    (substochastic : ∀ input, ENNReal.le
      (ENNReal.add (step input Set.univ) (exit input Set.univ)) ENNReal.one) :
    IsFinite step ∧ IsFinite exit := by
  constructor
  · refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
    intro input
    have included := ENNReal.addLeAddLeft (ENNReal.zeroLe (exit input Set.univ))
      (step input Set.univ)
    rw [ENNReal.addZero] at included
    exact ENNReal.leTrans included (substochastic input)
  · refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
    intro input
    have included := ENNReal.addLeAddRight (ENNReal.zeroLe (step input Set.univ))
      (exit input Set.univ)
    rw [ENNReal.zeroAdd] at included
    exact ENNReal.leTrans included (substochastic input)

/-- Subprobability continuation mass decreases with each further step. -/
public theorem iterate_mass_antitone (step : Kernel source source)
    (bounded : ∀ input, ENNReal.le (step input Set.univ) ENNReal.one)
    {first second : Nat} (included : first ≤ second) (input : alpha) :
    ENNReal.le (iterate step second input Set.univ) (iterate step first input Set.univ) := by
  have successor : ∀ count, ENNReal.le (iterate step (count + 1) input Set.univ)
      (iterate step count input Set.univ) := by
    intro count
    rw [iterate_succ_right, comp_apply_measurable _ _ _ source.univ]
    have bound := lintegral_mono (iterate step count input) bounded
    rw [lintegral_const, ENNReal.oneMul] at bound
    exact bound
  induction second with
  | zero =>
    have equal : first = 0 := by omega
    rw [equal]
    exact ENNReal.leRefl _
  | succ second induction =>
    by_cases equal : first = second + 1
    · rw [equal]
      exact ENNReal.leRefl _
    · exact ENNReal.leTrans (successor second) (induction (by omega))

/-- Under conservation, output mass is the complement of the limiting continuation mass. -/
public theorem loop_mass_eq_one_sub_iInf (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (input : alpha) :
    loop step exit input Set.univ = ENNReal.sub ENNReal.one
      (ENNReal.iInf (fun count => iterate step count input Set.univ)) := by
  rw [loop_eq_iSup_prefixApproximant step exit input target.univ, ENNReal.subIInf]
  apply congrArg ENNReal.iSup
  funext count
  have balance := prefix_mass_eq_one step exit conservative count input
  have residualBound := ENNReal.addLeAddRight
    (ENNReal.zeroLe (prefixApproximant step exit count input Set.univ))
    (iterate step count input Set.univ)
  rw [ENNReal.zeroAdd, balance] at residualBound
  have finite := ENNReal.finiteOfLe residualBound (show ENNReal.Finite ENNReal.one from True.intro)
  rw [← balance, ENNReal.addSubCancelRight finite]

/-- Conservation separates total output mass from the mass that continues forever. -/
public theorem loop_mass_add_iInf_eq_one (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (input : alpha) :
    ENNReal.add (loop step exit input Set.univ)
      (ENNReal.iInf (fun count => iterate step count input Set.univ)) = ENNReal.one := by
  rw [loop_mass_eq_one_sub_iInf step exit conservative input]
  apply ENNReal.subAddCancel
  have initial := ENNReal.iInfLe (fun count => iterate step count input Set.univ) 0
  rw [iterate_zero, deterministic_apply, Measure.dirac_apply_univ] at initial
  exact initial

/-- With conservation, mass-one output is equivalent to vanishing continuation mass. -/
public theorem loop_mass_one_iff (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (input : alpha) :
    loop step exit input Set.univ = ENNReal.one ↔
      ENNReal.iInf (fun count => iterate step count input Set.univ) = ENNReal.zero := by
  have balance := loop_mass_add_iInf_eq_one step exit conservative input
  constructor
  · intro outputOne
    rw [outputOne] at balance
    apply ENNReal.addLeftCancelOfFinite (show ENNReal.Finite ENNReal.one from True.intro)
    rw [ENNReal.addZero]
    exact balance
  · intro vanishing
    rw [vanishing, ENNReal.addZero] at balance
    exact balance

/-- Continuation mass vanishes from every state. -/
@[expose] public noncomputable def VanishingContinuation (step : Kernel source source) : Prop :=
  ∀ input, ENNReal.iInf (fun count => iterate step count input Set.univ) = ENNReal.zero

public theorem loop_mass_one_everywhere_iff (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one) :
    (∀ input, loop step exit input Set.univ = ENNReal.one) ↔ VanishingContinuation step := by
  constructor
  · intro outputOne input
    exact (loop_mass_one_iff step exit conservative input).mp (outputOne input)
  · intro vanishing input
    exact (loop_mass_one_iff step exit conservative input).mpr (vanishing input)

public theorem loop_isProbability (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (vanishing : VanishingContinuation step) (input : alpha) :
    Measure.IsProbability (loop step exit input) :=
  ⟨(loop_mass_one_iff step exit conservative input).mpr (vanishing input)⟩

end Foundations.Measure.Kernel
