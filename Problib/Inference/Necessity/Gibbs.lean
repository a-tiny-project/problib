module

public import Problib.Inference.Gibbs
public import Problib.Inference.Necessity.Weighting
set_option autoImplicit false

/-! Necessity for convergence of Gibbs scans.

`gibbs_scan_converges` needs the joint density bounded below by a positive
constant. Two bits constrained equal, against fair references, have joint
density one where the bits agree and zero where they differ, so the target puts
one half on each agreeing point. The density is at most one, and only the lower
bound fails. The Gibbs conditional at either bit, from a point where the bits
agree, is the Dirac measure at the common value, so each update keeps that
point. Both agreeing points are invariant under the scan, and the scan
converges from every law to no law.

Proofs are finite evaluations of Dirac sums. -/

namespace Problib.Inference.Necessity.Gibbs

open Problib.Real Problib.Measure
open Problib.Measure.Kernel (ConvergesFromEveryLaw)
open Problib.Measure.Kernel.Site
open Problib.Inference.Necessity.Weighting (bools fair halfMass lintegral_fair fair_probability
  halfMass_ne_zero)

public section

/-- Two sites, each a discrete bit. -/
abbrev bits : Bool → Space Bool := fun _ => bools

/-- The fair reference at each bit. -/
noncomputable abbrev fairs : ∀ index : Bool, Measure (bits index) := fun _ => fair bools false true

@[expose] noncomputable def fairsFinite : ∀ index : Bool, Measure.SFinite (fairs index) :=
  fun _ => Measure.SFinite.ofFinite (fair_probability bools false true).to_finite

/-- The points where the two bits agree. -/
@[expose] def agreeing : Set (Bool → Bool) := fun point => point false = point true

theorem agreeing_measurable : (Space.pi bits).Measurable agreeing := by
  have coordinate (site value : Bool) :
      (Space.pi bits).Measurable (fun point : Bool → Bool => point site = value) :=
    Space.coordinate_measurable bits site (set := fun bit : Bool => bit = value) True.intro
  have split : agreeing = Set.union
      (Set.inter (fun point : Bool → Bool => point false = false)
        (fun point : Bool → Bool => point true = false))
      (Set.inter (fun point : Bool → Bool => point false = true)
        (fun point : Bool → Bool => point true = true)) := by
    funext point
    apply propext
    show point false = point true ↔
      (point false = false ∧ point true = false) ∨ (point false = true ∧ point true = true)
    cases point false <;> cases point true <;> decide
  rw [split]
  exact (Space.pi bits).union
    ((Space.pi bits).inter (coordinate false false) (coordinate true false))
    ((Space.pi bits).inter (coordinate false true) (coordinate true true))

/-- The factor that is one where the bits agree and zero where they differ. -/
@[expose] noncomputable def equality : Factor bits where
  scope := Set.univ
  potential := ennrealIndicator agreeing (fun _ => ENNReal.one)
  measurable := ENNRealMeasurable.indicator agreeing_measurable (ENNRealMeasurable.constant _ _)
  reads := fun first second same => by
    rw [funext (fun index => same index True.intro)]

/-- The Gibbs scan over both bits for the equality factor. -/
@[expose] noncomputable def scan : Kernel (Space.pi bits) (Space.pi bits) :=
  sweep ([false, true].map (gibbsStep [equality] fairs fairsFinite (fun _ => false)))

/-- The point with both bits equal to `bit`. -/
@[expose] def both (bit : Bool) : Bool → Bool := fun _ => bit

theorem both_replace_agreeing (bit site value : Bool) :
    agreeing (replace (both bit) site value) ↔ value = bit := by
  cases site
  · show replace (both bit) false value false = replace (both bit) false value true ↔ value = bit
    rw [replace_same, replace_of_ne (both bit) value (show true ≠ false by decide)]
    exact Iff.rfl
  · show replace (both bit) true value false = replace (both bit) true value true ↔ value = bit
    rw [replace_same, replace_of_ne (both bit) value (show false ≠ true by decide)]
    exact ⟨Eq.symm, Eq.symm⟩

theorem both_line (bit site value : Bool) :
    joint [equality] (replace (both bit) site value) =
      if value = bit then ENNReal.one else ENNReal.zero := by
  show ENNReal.mul (equality.potential (replace (both bit) site value)) ENNReal.one = _
  rw [ENNReal.mul_one]
  show ennrealPiecewise agreeing (fun _ => ENNReal.one) (fun _ => ENNReal.zero)
    (replace (both bit) site value) = _
  unfold ennrealPiecewise
  by_cases same : value = bit
  · rw [ite_eq_left same, ite_eq_left ((both_replace_agreeing bit site value).mpr same)]
  · rw [ite_eq_right same,
      ite_eq_right (fun agree => same ((both_replace_agreeing bit site value).mp agree))]

/-- The line through an agreeing point carries half its mass, all at the common
value. -/
theorem both_fiber (bit site : Bool) :
    Kernel.densityFiber (fairs site)
        (fun point value => joint [equality] (replace point site value)) (both bit) =
      Measure.smul halfMass (Measure.dirac bools bit) := by
  apply Measure.ext
  intro set setMeasurable
  unfold Kernel.densityFiber
  rw [Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable,
    lintegral_fair _ _ _ (fun _ => Space.discrete_measurable _),
    Measure.smul_apply_measurable _ _ setMeasurable, Measure.dirac_apply _ _ setMeasurable]
  congr 1
  unfold ennrealIndicator ennrealPiecewise
  simp only [both_line]
  cases bit <;> by_cases atFalse : set false <;> by_cases atTrue : set true <;>
    simp [atFalse, atTrue, ENNReal.add_zero, ENNReal.zero_add]

/-- From an agreeing point, the Gibbs conditional at either bit is the Dirac
measure at the common value. -/
theorem both_conditional (bit site : Bool) :
    conditional [equality] fairs fairsFinite (fun _ => false) site (both bit) =
      Measure.dirac bools bit := by
  have mass : Kernel.densityFiber (fairs site)
      (fun point value => joint [equality] (replace point site value)) (both bit) Set.univ =
      halfMass := by
    rw [both_fiber, Measure.smul_apply_measurable _ _ bools.univ, Measure.dirac_apply_univ,
      ENNReal.mul_one]
  have defined : Measure.IsNormalizable (Kernel.densityFiber (fairs site)
      (fun point value => joint [equality] (replace point site value)) (both bit)) :=
    ⟨⟨by rw [mass]; exact True.intro⟩, by rw [mass]; exact halfMass_ne_zero⟩
  unfold conditional
  rw [Kernel.densityConditional_eq_normalize _ _ _ _ _ defined]
  apply Measure.normalize_eq_of_smul_eq
  rw [mass, both_fiber]

/-- Each Gibbs update keeps an agreeing point. -/
theorem both_gibbsStep (bit site : Bool) :
    (gibbsStep [equality] fairs fairsFinite (fun _ => false) site).run (both bit) =
      Measure.dirac (Space.pi bits) (both bit) := by
  rw [gibbsStep_run_apply, both_conditional, Measure.map_dirac]
  congr 1
  funext index
  by_cases same : index = site
  · subst same
    exact replace_same _ _ _
  · exact replace_of_ne _ _ same

/-- The scan keeps each agreeing point. -/
theorem both_invariant (bit : Bool) :
    (Measure.dirac (Space.pi bits) (both bit)).bind scan =
      Measure.dirac (Space.pi bits) (both bit) := by
  apply sweep_invariant
  intro step member
  obtain ⟨site, _, rfl⟩ := List.mem_map.mp member
  rw [Measure.dirac_bind, both_gibbsStep]

/-- `gibbs_scan_converges` needs the joint density bounded below by a positive
constant. With two bits constrained equal, both points where the bits agree are
invariant under the Gibbs scan, so it converges from every law to no law. -/
theorem vanishing_density_does_not_converge : ¬∃ law, ConvergesFromEveryLaw scan law := by
  rintro ⟨law, converges⟩
  have atFalse := converges.invariant_unique
    ⟨Measure.dirac (Space.pi bits) (both false), Measure.IsProbability.dirac _ _⟩
    (both_invariant false)
  have atTrue := converges.invariant_unique
    ⟨Measure.dirac (Space.pi bits) (both true), Measure.IsProbability.dirac _ _⟩
    (both_invariant true)
  have setMeasurable : (Space.pi bits).Measurable (fun point : Bool → Bool => point false = true) :=
    Space.coordinate_measurable bits false (set := fun value : Bool => value = true) True.intro
  have evaluated := congrArg
    (fun law : Giry.Law (Space.pi bits) => law.val (fun point : Bool → Bool => point false = true))
    (atFalse.trans atTrue.symm)
  simp only at evaluated
  rw [Measure.dirac_apply_of_not_mem _ _ setMeasurable (by decide),
    Measure.dirac_apply_of_mem _ _ setMeasurable (by decide)] at evaluated
  exact ENNReal.one_ne_zero evaluated.symm

end

end Problib.Inference.Necessity.Gibbs
