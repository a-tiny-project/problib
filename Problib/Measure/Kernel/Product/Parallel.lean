module

public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Finite
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Iteration.Basic
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Measurability

set_option autoImplicit false

/-!
# Independent pair kernels

`parallel` runs two kernels side by side, one on each coordinate of a pair.
Its fiber at `(x, y)` is the product of the two fibers. Rectangles evaluate to
products, each coordinate marginal is the other fiber's mass times one fiber,
and the construction commutes with composition, iteration and invariance.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v w x
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {first : Space α} {second : Space β} {left : Space γ} {right : Space δ}

private theorem parallel_fiber_measurable (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    {event : Set (γ × δ)}
    (eventMeasurable : (Space.product left right).Measurable event) :
    ENNRealMeasurable (Space.product first second) (fun input =>
      lintegral (leftKernel input.1) (fun value =>
        rightKernel input.2
          (Set.preimage (fun other => (value, other)) event))) := by
  let shifted : Kernel (Space.product (Space.product first second) left) right :=
    rightKernel.precomp (fun state => state.1.2)
      (MeasurableMap.comp (Space.second_measurable first second)
        (Space.first_measurable (Space.product first second) left))
  have lifted : ENNRealMeasurable
      (Space.product (Space.product first second) left)
      (fun state => shifted state
        (verticalSection
          (Set.preimage (fun point : ((α × β) × γ) × δ => (point.1.2, point.2))
            event) state)) :=
    section_apply_measurable_of_finite_fibers shifted
      (fun state => rightFinite state.1.2)
      ((by measurability : MeasurableMap _ _
        fun point : ((α × β) × γ) × δ => (point.1.2, point.2)) eventMeasurable)
  exact lintegral_measurable_joint
    (leftKernel.precomp Prod.fst (Space.first_measurable first second))
    (IsSFinite.ofFiniteFibers (fun input => leftFinite input.1))
    (function := fun input value =>
      rightKernel input.2 (Set.preimage (fun other => (value, other)) event))
    lifted

/-- Two kernels run independently, one per coordinate. The fiber at `(x, y)` is
the product of `leftKernel x` and `rightKernel y`. -/
@[expose] public noncomputable def parallel (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input)) :
    Kernel (Space.product first second) (Space.product left right) where
  toFun := fun input => Measure.prod (leftKernel input.1) (rightKernel input.2)
    (Measure.SFinite.ofFinite (rightFinite input.2))
  measurable := by
    intro event eventMeasurable
    have equal : (fun input : α × β =>
        Measure.prod (leftKernel input.1) (rightKernel input.2)
          (Measure.SFinite.ofFinite (rightFinite input.2)) event) =
        (fun input => lintegral (leftKernel input.1) (fun value =>
          rightKernel input.2
            (Set.preimage (fun other => (value, other)) event))) := by
      funext input
      exact Measure.prod_apply _ _ _ eventMeasurable
    rw [equal]
    exact parallel_fiber_measurable leftKernel rightKernel leftFinite
      rightFinite eventMeasurable

public theorem parallel_apply (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (input : α × β) :
    parallel leftKernel rightKernel leftFinite rightFinite input =
      Measure.prod (leftKernel input.1) (rightKernel input.2)
        (Measure.SFinite.ofFinite (rightFinite input.2)) :=
  rfl

private theorem prod_congr_measures {firstLeft secondLeft : Measure left}
    {firstRight secondRight : Measure right}
    (leftEqual : firstLeft = secondLeft) (rightEqual : firstRight = secondRight)
    (firstFinite : Measure.SFinite firstRight)
    (secondFinite : Measure.SFinite secondRight) :
    Measure.prod firstLeft firstRight firstFinite =
      Measure.prod secondLeft secondRight secondFinite := by
  subst leftEqual
  subst rightEqual
  exact Measure.prod_certificate_irrelevant _ _ _ _

/-- Equal kernels give equal pair kernels, whatever finiteness proofs are
supplied. -/
public theorem parallel_congr {leftKernel leftKernel' : Kernel first left}
    {rightKernel rightKernel' : Kernel second right}
    (leftEqual : leftKernel = leftKernel')
    (rightEqual : rightKernel = rightKernel')
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftFinite' : ∀ input, Measure.IsFinite (leftKernel' input))
    (rightFinite' : ∀ input, Measure.IsFinite (rightKernel' input)) :
    parallel leftKernel rightKernel leftFinite rightFinite =
      parallel leftKernel' rightKernel' leftFinite' rightFinite' := by
  subst leftEqual
  subst rightEqual
  rfl

public theorem parallel_apply_product (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (input : α × β) {leftSet : Set γ} {rightSet : Set δ}
    (leftMeasurable : left.Measurable leftSet)
    (rightMeasurable : right.Measurable rightSet) :
    parallel leftKernel rightKernel leftFinite rightFinite input
        (Set.product leftSet rightSet) =
      ENNReal.mul (leftKernel input.1 leftSet) (rightKernel input.2 rightSet) :=
  Measure.prod_apply_product _ _ _ leftMeasurable rightMeasurable

public theorem parallel_map_fst (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (input : α × β) :
    (parallel leftKernel rightKernel leftFinite rightFinite input).map Prod.fst
        (Space.first_measurable left right) =
      Measure.smul (rightKernel input.2 Set.univ) (leftKernel input.1) := by
  apply Measure.ext
  intro set setMeasurable
  have preimage : Set.preimage Prod.fst set =
      Set.product set (Set.univ : Set δ) := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member, True.intro⟩, fun member => member.1⟩
  rw [Measure.map_apply _ _ _ setMeasurable, preimage,
    parallel_apply_product _ _ _ _ _ setMeasurable right.univ,
    Measure.smul_apply_measurable _ _ setMeasurable, ENNReal.mul_comm]

public theorem parallel_map_snd (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (input : α × β) :
    (parallel leftKernel rightKernel leftFinite rightFinite input).map Prod.snd
        (Space.second_measurable left right) =
      Measure.smul (leftKernel input.1 Set.univ) (rightKernel input.2) := by
  apply Measure.ext
  intro set setMeasurable
  have preimage : Set.preimage Prod.snd set =
      Set.product (Set.univ : Set γ) set := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨True.intro, member⟩, fun member => member.2⟩
  rw [Measure.map_apply _ _ _ setMeasurable, preimage,
    parallel_apply_product _ _ _ _ _ left.univ setMeasurable,
    Measure.smul_apply_measurable _ _ setMeasurable]

public theorem parallel_le_parallel {leftKernel leftKernel' : Kernel first left}
    {rightKernel rightKernel' : Kernel second right}
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftFinite' : ∀ input, Measure.IsFinite (leftKernel' input))
    (rightFinite' : ∀ input, Measure.IsFinite (rightKernel' input))
    (leftLe : Kernel.le leftKernel leftKernel')
    (rightLe : Kernel.le rightKernel rightKernel') :
    Kernel.le (parallel leftKernel rightKernel leftFinite rightFinite)
      (parallel leftKernel' rightKernel' leftFinite' rightFinite') := by
  intro input event eventMeasurable
  rw [parallel_apply, parallel_apply,
    Measure.prod_apply _ _ _ eventMeasurable,
    Measure.prod_apply _ _ _ eventMeasurable]
  exact ENNReal.le_trans
    (lintegral_mono _ (fun value => rightLe input.2 _
      (verticalSection_measurable eventMeasurable value)))
    (lintegral_mono_measure _ _ _ (leftLe input.1))

/-- Binding a product measure against a pair kernel gives the product of the
two bound marginals. -/
public theorem prod_bind_parallel (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftMeasure : Measure first) (rightMeasure : Measure second)
    (rightMeasureFinite : Measure.IsFinite rightMeasure)
    (leftBindFinite : Measure.IsFinite (leftMeasure.bind leftKernel))
    (rightBindFinite : Measure.IsFinite (rightMeasure.bind rightKernel)) :
    (Measure.prod leftMeasure rightMeasure
        (Measure.SFinite.ofFinite rightMeasureFinite)).bind
        (parallel leftKernel rightKernel leftFinite rightFinite) =
      Measure.prod (leftMeasure.bind leftKernel) (rightMeasure.bind rightKernel)
        (Measure.SFinite.ofFinite rightBindFinite) := by
  rw [Measure.prod_certificate_irrelevant _ _
    (Measure.SFinite.ofFinite rightBindFinite)
    (Measure.SigmaFinite.ofFinite rightBindFinite).toSFinite]
  apply Measure.prod_unique (Measure.SigmaFinite.ofFinite leftBindFinite)
    (Measure.SigmaFinite.ofFinite rightBindFinite)
  intro leftSet rightSet leftMeasurable rightMeasurable
  have leftEvaluation := leftKernel.measurable leftMeasurable
  have rightEvaluation := rightKernel.measurable rightMeasurable
  rw [Measure.bind_apply _ _
      (Space.product_set_measurable left right leftMeasurable rightMeasurable),
    Measure.bind_apply _ _ leftMeasurable, Measure.bind_apply _ _ rightMeasurable]
  calc
    lintegral
        (Measure.prod leftMeasure rightMeasure
          (Measure.SFinite.ofFinite rightMeasureFinite))
        (fun input => parallel leftKernel rightKernel leftFinite rightFinite
          input (Set.product leftSet rightSet)) =
        lintegral
          (Measure.prod leftMeasure rightMeasure
            (Measure.SFinite.ofFinite rightMeasureFinite))
          (fun input => ENNReal.mul (leftKernel input.1 leftSet)
            (rightKernel input.2 rightSet)) := by
      apply lintegral_congr
      intro input
      exact parallel_apply_product _ _ _ _ input leftMeasurable rightMeasurable
    _ = lintegral leftMeasure (fun value =>
          lintegral rightMeasure (fun other =>
            ENNReal.mul (leftKernel value leftSet) (rightKernel other rightSet))) :=
      lintegral_prod _ _ _
        (ENNRealMeasurable.mul
          (ENNRealMeasurable.comp leftEvaluation (Space.first_measurable first second))
          (ENNRealMeasurable.comp rightEvaluation (Space.second_measurable first second)))
    _ = lintegral leftMeasure (fun value =>
          ENNReal.mul (leftKernel value leftSet)
            (lintegral rightMeasure (fun other => rightKernel other rightSet))) := by
      apply lintegral_congr
      intro value
      exact lintegral_smul _ _ rightEvaluation
    _ = ENNReal.mul
          (lintegral leftMeasure (fun value => leftKernel value leftSet))
          (lintegral rightMeasure (fun other => rightKernel other rightSet)) := by
      rw [ENNReal.mul_comm, ← lintegral_smul _ _ leftEvaluation]
      apply lintegral_congr
      intro value
      exact ENNReal.mul_comm _ _

public theorem parallel_comp {leftKernel : Kernel first first}
    {rightKernel : Kernel second second}
    {leftNext : Kernel first left} {rightNext : Kernel second right}
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftNextFinite : ∀ input, Measure.IsFinite (leftNext input))
    (rightNextFinite : ∀ input, Measure.IsFinite (rightNext input))
    (leftCompFinite : ∀ input, Measure.IsFinite (leftKernel.comp leftNext input))
    (rightCompFinite : ∀ input, Measure.IsFinite (rightKernel.comp rightNext input)) :
    (parallel leftKernel rightKernel leftFinite rightFinite).comp
        (parallel leftNext rightNext leftNextFinite rightNextFinite) =
      parallel (leftKernel.comp leftNext) (rightKernel.comp rightNext)
        leftCompFinite rightCompFinite := by
  apply Kernel.ext
  intro input
  rw [comp_apply, parallel_apply, parallel_apply,
    prod_bind_parallel _ _ _ _ _ _ (rightFinite input.2)
      (leftCompFinite input.1) (rightCompFinite input.2)]
  exact prod_congr_measures (comp_apply _ _ _).symm (comp_apply _ _ _).symm _ _

private theorem parallel_identity :
    parallel (Kernel.deterministic (fun value => value) (MeasurableMap.identity first))
        (Kernel.deterministic (fun value => value) (MeasurableMap.identity second))
        (fun input => Measure.IsFinite.dirac first input)
        (fun input => Measure.IsFinite.dirac second input) =
      Kernel.deterministic (fun value => value)
        (MeasurableMap.identity (Space.product first second)) := by
  apply Kernel.ext
  intro input
  rw [parallel_apply, Kernel.deterministic_apply (fun value => value)
      (MeasurableMap.identity (Space.product first second)),
    prod_congr_measures (Kernel.deterministic_apply _ _ input.1)
      (Kernel.deterministic_apply _ _ input.2) _
      (Measure.SigmaFinite.ofFinite (Measure.IsFinite.dirac second input.2)).toSFinite]
  symm
  apply Measure.prod_unique
    (Measure.SigmaFinite.ofFinite (Measure.IsFinite.dirac first input.1))
    (Measure.SigmaFinite.ofFinite (Measure.IsFinite.dirac second input.2))
  intro leftSet rightSet leftMeasurable rightMeasurable
  classical
  rw [Measure.dirac_apply _ _
      (Space.product_set_measurable first second leftMeasurable rightMeasurable),
    Measure.dirac_apply _ _ leftMeasurable, Measure.dirac_apply _ _ rightMeasurable]
  by_cases leftMember : leftSet input.1
  · by_cases rightMember : rightSet input.2
    · rw [ite_eq_left ⟨leftMember, rightMember⟩, ite_eq_left leftMember, ite_eq_left rightMember,
        ENNReal.one_mul]
    · rw [ite_eq_right (fun member => rightMember member.2), ite_eq_left leftMember,
        ite_eq_right rightMember, ENNReal.one_mul]
  · rw [ite_eq_right (fun member => leftMember member.1), ite_eq_right leftMember,
      ENNReal.zero_mul]

/-- Iterating a pair of Markov kernels iterates each coordinate. -/
public theorem iterate_parallel {leftKernel : Kernel first first}
    {rightKernel : Kernel second second}
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftIterateFinite : ∀ count input,
      Measure.IsFinite (iterate leftKernel count input))
    (rightIterateFinite : ∀ count input,
      Measure.IsFinite (iterate rightKernel count input))
    (count : Nat) :
    iterate (parallel leftKernel rightKernel leftFinite rightFinite) count =
      parallel (iterate leftKernel count) (iterate rightKernel count)
        (leftIterateFinite count) (rightIterateFinite count) := by
  induction count with
  | zero =>
      rw [iterate_zero, parallel_congr (iterate_zero leftKernel)
        (iterate_zero rightKernel) _ _
        (fun input => Measure.IsFinite.dirac first input)
        (fun input => Measure.IsFinite.dirac second input), parallel_identity]
  | succ count induction =>
      rw [iterate_succ, induction,
        parallel_comp leftFinite rightFinite _ _
          (fun input => by
            rw [← iterate_succ]
            exact leftIterateFinite (count + 1) input)
          (fun input => by
            rw [← iterate_succ]
            exact rightIterateFinite (count + 1) input)]
      exact parallel_congr (iterate_succ leftKernel count).symm
        (iterate_succ rightKernel count).symm _ _ _ _

/-- A product of two invariant finite measures is invariant for the pair
kernel. -/
public theorem parallel_invariant {leftKernel : Kernel first first}
    {rightKernel : Kernel second second}
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (leftMeasure : Measure first) (rightMeasure : Measure second)
    (leftMeasureFinite : Measure.IsFinite leftMeasure)
    (rightMeasureFinite : Measure.IsFinite rightMeasure)
    (leftInvariant : leftMeasure.bind leftKernel = leftMeasure)
    (rightInvariant : rightMeasure.bind rightKernel = rightMeasure) :
    (Measure.prod leftMeasure rightMeasure
        (Measure.SFinite.ofFinite rightMeasureFinite)).bind
        (parallel leftKernel rightKernel leftFinite rightFinite) =
      Measure.prod leftMeasure rightMeasure
        (Measure.SFinite.ofFinite rightMeasureFinite) := by
  rw [prod_bind_parallel _ _ _ _ _ _ rightMeasureFinite
    (by rw [leftInvariant]; exact leftMeasureFinite)
    (by rw [rightInvariant]; exact rightMeasureFinite)]
  exact prod_congr_measures leftInvariant rightInvariant _ _

/-- The total mass of a pair-kernel fiber is the product of the two masses. -/
public theorem parallel_apply_univ (leftKernel : Kernel first left)
    (rightKernel : Kernel second right)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input))
    (input : α × β) :
    parallel leftKernel rightKernel leftFinite rightFinite input Set.univ =
      ENNReal.mul (leftKernel input.1 Set.univ) (rightKernel input.2 Set.univ) := by
  have whole : (Set.univ : Set (γ × δ)) = Set.product Set.univ Set.univ := by
    apply Set.ext
    intro value
    exact ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩
  rw [whole]
  exact parallel_apply_product _ _ _ _ input left.univ right.univ

/-- A pair of Markov kernels is Markov. -/
public theorem parallel_isProbability {leftKernel : Kernel first left}
    {rightKernel : Kernel second right}
    (leftMarkov : ∀ input, Measure.IsProbability (leftKernel input))
    (rightMarkov : ∀ input, Measure.IsProbability (rightKernel input))
    (input : α × β) :
    Measure.IsProbability (parallel leftKernel rightKernel
      (fun input => (leftMarkov input).to_finite)
      (fun input => (rightMarkov input).to_finite) input) := by
  constructor
  rw [parallel_apply_univ, (leftMarkov input.1).univ_eq_one,
    (rightMarkov input.2).univ_eq_one, ENNReal.mul_one]

end Problib.Measure.Kernel

namespace Problib.Measure.Measure

open Problib.Real

universe u v
variable {α : Type u} {β : Type v} {first : Space α} {second : Space β}

/-- Two almost-everywhere properties hold together almost everywhere on the
product measure. -/
public theorem AE.prod {left : Measure first} {right : Measure second}
    (rightFinite : IsFinite right) {leftHolds : α → Prop} {rightHolds : β → Prop}
    (leftAE : left.AE leftHolds) (rightAE : right.AE rightHolds) :
    (Measure.prod left right (SFinite.ofFinite rightFinite)).AE
      (fun pair => leftHolds pair.1 ∧ rightHolds pair.2) := by
  classical
  rcases leftAE.exists_null_exception with
    ⟨leftBad, leftMeasurable, leftNull, leftExcept⟩
  rcases rightAE.exists_null_exception with
    ⟨rightBad, rightMeasurable, rightNull, rightExcept⟩
  apply NullSet.mono (right := Set.union (Set.product leftBad Set.univ)
    (Set.product Set.univ rightBad))
  · apply NullSet.union
    · show Measure.prod left right _ (Set.product leftBad Set.univ) = ENNReal.zero
      rw [prod_apply_product _ _ _ leftMeasurable second.univ]
      rw [show left leftBad = ENNReal.zero from leftNull, ENNReal.zero_mul]
    · show Measure.prod left right _ (Set.product Set.univ rightBad) = ENNReal.zero
      rw [prod_apply_product _ _ _ first.univ rightMeasurable]
      rw [show right rightBad = ENNReal.zero from rightNull, ENNReal.mul_zero]
  · intro pair failing
    by_cases leftFails : leftBad pair.1
    · exact Or.inl ⟨leftFails, True.intro⟩
    · refine Or.inr ⟨True.intro, ?_⟩
      by_cases rightFails : rightBad pair.2
      · exact rightFails
      · exact absurd ⟨leftExcept _ leftFails, rightExcept _ rightFails⟩ failing

end Problib.Measure.Measure
