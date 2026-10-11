module

public import Problib.Countable.Bijection
public import Problib.Inference.Invariance
public import Problib.Inference.Necessity.Weighting
public import Problib.Inference.SplitMerge.Kernel
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Space.Countable

set_option autoImplicit false

/-!
# Why split/merge moves take the shape they do

A kernel that leaves a fixed-count target invariant keeps the count from
almost every start (`fixed_count_rejects`). So a target spread over several
counts needs a move that changes the count.

A merge that keeps only the combined strength of two entries sends distinct
states to one state. No involution extends it (`forgetfulMerge_not_involution`),
so it cannot be the forward map of a split/merge pairing, whose inverse must
recover every state in its domain.

The acceptance needs the reverse selection density and the whole-state
density. On lists of units, with half the target on `[()]` and half on
`[(), ()]`, a kernel that omits the merge's selection probability one half
leaves mass one quarter on `[()]`, against one half under the target
(`omitted_reverse_selection_not_invariant`). On lists of Booleans, a density
that scores only the last element sends mass one eighth to `[false, true]`,
which the target does not charge (`pair_local_ratio_not_invariant`).

Both kernels use the append move (`AppendMove.move`): a split appends an
element to a one-element list, and a merge drops the last element of a
two-element list. Proofs are finite evaluations of Dirac sums.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {space : Space α}

public section

/-- A kernel that leaves a fixed-count target invariant moves off that count
with probability zero, from almost every start. -/
theorem fixed_count_rejects {target : Measure space} {kernel : Kernel space space}
    {count : α → Nat} (countMeasurable : MeasurableMap space (Space.discrete Nat) count)
    {fixedCount : Nat} (invariant : KernelInvariant target kernel)
    (fixed : target (fun state => count state ≠ fixedCount) = ENNReal.zero) :
    target.AEEq (fun state => kernel state (fun next => count next ≠ fixedCount))
      (fun _ => ENNReal.zero) := by
  have regionMeasurable : space.Measurable (fun next => count next ≠ fixedCount) :=
    countMeasurable (set := fun value => value ≠ fixedCount) trivial
  apply (lintegral_eq_zero_iff (kernel.measurable regionMeasurable)).mp
  rw [← Measure.bind_apply target kernel regionMeasurable]
  unfold KernelInvariant at invariant
  rw [invariant]
  exact fixed

/-- The merge that keeps only the combined strength of the first two entries. -/
@[expose] def forgetfulMerge : List Nat → List Nat
  | first :: second :: rest => (first + second) :: rest
  | values => values

/-- No involution of the extended states extends a merge that forgets its
residual: `[1, 2]` and `[0, 3]` merge to the same state. -/
theorem forgetfulMerge_not_involution :
    ¬ ∃ involution : List Nat × Sum Unit Unit → List Nat × Sum Unit Unit,
      (∀ point, involution (involution point) = point) ∧
      ∀ values, 2 ≤ values.length →
        involution (values, Sum.inr ()) = (forgetfulMerge values, Sum.inl ()) := by
  rintro ⟨involution, involutive, merges⟩
  have first := merges [1, 2] (by decide)
  have second := merges [0, 3] (by decide)
  have same : involution ([1, 2], Sum.inr ()) = involution ([0, 3], Sum.inr ()) := by
    rw [first, second]
    rfl
  have equal := congrArg involution same
  rw [involutive, involutive] at equal
  exact absurd (congrArg Prod.fst equal) (by decide)

namespace AppendMove

open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel)
open Problib.Inference.Necessity.Weighting (halfMass fair fair_probability lintegral_fair
  half_ofRat)

/-- Lists over a coded alphabet, coded injectively into `Nat`. -/
private def listCode {E : Type} (code : E → Nat) : List E → Nat
  | [] => 0
  | head :: tail => Countable.Pair.encode (code head, listCode code tail) + 1

private theorem listCode_injective {E : Type} {code : E → Nat}
    (injective : Function.Injective code) : Function.Injective (listCode code) := by
  intro left
  induction left with
  | nil =>
    intro right same
    cases right with
    | nil => rfl
    | cons _ _ => exact absurd same (by simp [listCode])
  | cons head tail tailInjective =>
    intro right same
    cases right with
    | nil => exact absurd same (by simp [listCode])
    | cons other rest =>
      have step : Countable.Pair.encode (code head, listCode code tail) =
          Countable.Pair.encode (code other, listCode code rest) := by
        simp only [listCode] at same
        omega
      have pair := Countable.Pair.encode_injective step
      rw [injective (congrArg Prod.fst pair), tailInjective (congrArg Prod.snd pair)]

theorem toNat_injective : Function.Injective Bool.toNat := by
  intro left right same
  cases left <;> cases right <;> first | rfl | exact absurd same (by decide)

private def sumCode {E : Type} (code : E → Nat) : Sum E Bool → Nat
  | .inl element => 2 * code element
  | .inr coin => 2 * coin.toNat + 1

private theorem sumCode_injective {E : Type} {code : E → Nat}
    (injective : Function.Injective code) : Function.Injective (sumCode code) := by
  rintro (left | left) (right | right) same <;> simp only [sumCode] at same
  · rw [injective (by omega : code left = code right)]
  · omega
  · omega
  · rw [toNat_injective (by omega : left.toNat = right.toNat)]

private theorem pairCode_injective {E B : Type} {code : E → Nat}
    (injective : Function.Injective code) {secondCode : B → Nat}
    (secondInjective : Function.Injective secondCode) :
    Function.Injective (fun point : List E × B =>
      Countable.Pair.encode (listCode code point.1, secondCode point.2)) := by
  intro left right same
  have pair := Countable.Pair.encode_injective same
  exact Prod.ext (listCode_injective injective (congrArg Prod.fst pair))
    (secondInjective (congrArg Prod.snd pair))

/-- Every set of a product of spaces whose sets are all measurable, with an
injective code into `Nat`, is measurable: it is a countable union of
measurable points. -/
private theorem product_measurable {A B : Type} {left : Space A} {right : Space B}
    (leftAll : ∀ set, left.Measurable set) (rightAll : ∀ set, right.Measurable set)
    (pointCode : A × B → Nat) (pointInjective : Function.Injective pointCode)
    (set : Set (A × B)) : (Space.product left right).Measurable set := by
  have points := Space.i_union_of_nat_injection (Space.product left right) pointCode
    pointInjective
    (fun point => Set.product (fun first => set point ∧ first = point.1)
      (fun second => second = point.2))
    (fun _ => Space.product_set_measurable left right (leftAll _) (rightAll _))
  have same : (fun value => ∃ point, Set.product (fun first => set point ∧ first = point.1)
      (fun second => second = point.2) value) = set := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨point, ⟨inside, first⟩, second⟩
      have equal : value = point := Prod.ext first second
      exact equal ▸ inside
    · intro inside
      exact ⟨value, ⟨inside, rfl⟩, rfl⟩
  rw [← same]
  exact points

theorem split_measurable {E : Type} (code : E → Nat) (injective : Function.Injective code)
    (set : Set (List E × E)) :
    (Space.product (Space.discrete (List E)) (Space.discrete E)).Measurable set :=
  product_measurable (fun _ => Space.discrete_measurable _)
    (fun _ => Space.discrete_measurable _) _ (pairCode_injective injective injective) set

theorem merge_measurable {E : Type} (code : E → Nat) (injective : Function.Injective code)
    (set : Set (List E × Bool)) :
    (Space.product (Space.discrete (List E)) (Space.discrete Bool)).Measurable set :=
  product_measurable (fun _ => Space.discrete_measurable _)
    (fun _ => Space.discrete_measurable _) _ (pairCode_injective injective toNat_injective) set

theorem extended_measurable {E : Type} (code : E → Nat) (injective : Function.Injective code)
    (set : Set (List E × Sum E Bool)) :
    (Space.product (Space.discrete (List E))
      (Space.sum (Space.discrete E) (Space.discrete Bool))).Measurable set :=
  product_measurable (right := Space.sum (Space.discrete E) (Space.discrete Bool))
    (fun _ => Space.discrete_measurable _)
    (fun _ => ⟨Space.discrete_measurable _, Space.discrete_measurable _⟩) _
    (pairCode_injective injective (sumCode_injective injective)) set

/-- Append on one-element lists, and drop the last element of two-element
lists marked `true`. -/
@[expose] def pairing {E : Type} (code : E → Nat) (injective : Function.Injective code)
    (fallback : E) :
    MeasurablePartialEquivalence (Space.product (Space.discrete (List E)) (Space.discrete E))
      (Space.product (Space.discrete (List E)) (Space.discrete Bool)) where
  forward := fun point => (point.1 ++ [point.2], true)
  inverse := fun point => (point.1.dropLast, point.1.getLastD fallback)
  sourceDomain := fun point => point.1.length = 1
  targetDomain := fun point => point.1.length = 2 ∧ point.2 = true
  sourceMeasurable := split_measurable code injective _
  targetMeasurable := merge_measurable code injective _
  forward_mem := fun point (single : point.1.length = 1) => ⟨by simp [single], rfl⟩
  inverse_mem := fun point (member : point.1.length = 2 ∧ point.2 = true) => by
    simp [member.1]
  inverse_forward := by
    rintro ⟨values, element⟩ _
    simp
  forward_inverse := by
    rintro ⟨values, coin⟩ ⟨pair, marked⟩
    subst marked
    rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals first | rfl | simp at pair
  forwardMeasurable := fun _ => split_measurable code injective _
  inverseMeasurable := fun _ => merge_measurable code injective _

/-- The append move. -/
@[expose] def move {E : Type} (code : E → Nat) (injective : Function.Injective code)
    (fallback : E) :
    SplitMergeMove (Space.discrete (List E)) (Space.discrete E) (Space.discrete Bool) :=
  ⟨pairing code injective fallback⟩

section Evaluation

variable {E : Type} (code : E → Nat) (injective : Function.Injective code) (fallback : E)

theorem involution_split (first element : E) :
    (move code injective fallback).involution ([first], .inl element) =
      ([first, element], .inr true) := by
  simp [SplitMergeMove.involution, SplitMergeMove.sideInvolution, sumDistribution, move,
    pairing]

theorem involution_merge (first second : E) :
    (move code injective fallback).involution ([first, second], .inr true) =
      ([first], .inl second) := by
  simp [SplitMergeMove.involution, SplitMergeMove.sideInvolution, sumDistribution, move,
    pairing]

theorem involution_stay_single (first : E) (coin : Bool) :
    (move code injective fallback).involution ([first], .inr coin) = ([first], .inr coin) := by
  simp [SplitMergeMove.involution, SplitMergeMove.sideInvolution, sumDistribution, move,
    pairing]

theorem involution_stay_unmarked (first second : E) :
    (move code injective fallback).involution ([first, second], .inr false) =
      ([first, second], .inr false) := by
  simp [SplitMergeMove.involution, SplitMergeMove.sideInvolution, sumDistribution, move,
    pairing]

end Evaluation

/-- A unit factor makes every Jacobian one. -/
private theorem jacobian_one {X A B : Type} {space : Space X} {splitAux : Space A}
    {mergeAux : Space B} (splitMerge : SplitMergeMove space splitAux mergeAux)
    (point : X × Sum A B) :
    splitMerge.jacobian (fun _ => Dedekind.one) point = Dedekind.one := by
  unfold SplitMergeMove.jacobian SplitMergeMove.sideJacobian
  generalize (sumDistribution space splitAux mergeAux).forward point = side
  rcases side with side | side <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split <;>
    first | rfl | exact Dedekind.inverse_one

private theorem indicator_self {X : Type} (value : X) :
    ennrealIndicator (fun candidate => candidate = value) (fun _ => ENNReal.one) value =
      ENNReal.one :=
  ennrealIndicator_of_mem rfl

private theorem indicator_other {X : Type} {value other : X} (distinct : other ≠ value) :
    ennrealIndicator (fun candidate => candidate = value) (fun _ => ENNReal.one) other =
      ENNReal.zero :=
  ennrealIndicator_of_not_mem distinct

private theorem sum_ennreal {A B : Type} (function : Sum A B → ENNReal) :
    ENNRealMeasurable (Space.sum (Space.discrete A) (Space.discrete B)) function :=
  fun _ => ⟨Space.discrete_measurable _, Space.discrete_measurable _⟩

/-! ### Omitting the reverse selection -/

/-- The constant code is injective on units, since any two units are equal. -/
theorem unit_code_injective : Function.Injective fun _ : Unit => 0 :=
  fun _ _ _ => rfl

/-- The append move on lists of units. -/
abbrev unitMove : SplitMergeMove (Space.discrete (List Unit)) (Space.discrete Unit)
    (Space.discrete Bool) :=
  move (fun _ => 0) unit_code_injective ()

/-- Half on `[()]` and half on `[(), ()]`. -/
@[expose] noncomputable def unitTarget : Measure (Space.discrete (List Unit)) :=
  fair (Space.discrete (List Unit)) [()] [(), ()]

/-- One on lists of length one and two: the unit target's density against half
the counting measure. -/
@[expose] noncomputable def unitDensity : List Unit → Carrier
  | [_] | [_, _] => Dedekind.one
  | _ => Dedekind.zero

/-- One element splits. Two elements pick the merge's mark by a fair coin, so
the marked merge has probability one half. -/
@[expose] noncomputable def unitSelection :
    Kernel (Space.discrete (List Unit)) (Space.sum (Space.discrete Unit) (Space.discrete Bool)) :=
  Kernel.piecewise (fun values => values.length = 1) (Space.discrete_measurable _)
    (Kernel.const _ (Measure.dirac _ (.inl ())))
    (Kernel.const _ (fair _ (.inr true) (.inr false)))

@[expose] noncomputable def unitSelectionFinite : Kernel.IsSFinite unitSelection :=
  Kernel.IsSFinite.piecewise
    (Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite (Measure.IsProbability.dirac _ _).to_finite))
    (Kernel.IsSFinite.const _ (Measure.SFinite.ofFinite (fair_probability _ _ _).to_finite))
    _ _

/-- The split/merge kernel with selection density one: the merge's selection
probability one half is left out of the acceptance. -/
@[expose] noncomputable def omittedKernel :
    Kernel (Space.discrete (List Unit)) (Space.discrete (List Unit)) :=
  splitMergeKernel unitSelection unitSelectionFinite unitMove unitDensity
    (fun _ => Dedekind.one) (fun _ => Dedekind.one) (fun _ => Space.discrete_measurable _)
    (MeasurableMap.constant _ borel Dedekind.one) (MeasurableMap.constant _ borel Dedekind.one)

private theorem unitSelection_single :
    unitSelection [()] = Measure.dirac _ (.inl ()) :=
  Kernel.piecewise_apply_of_mem _ _ _ _ _ rfl

private theorem unitSelection_pair :
    unitSelection [(), ()] = fair _ (.inr true) (.inr false) :=
  Kernel.piecewise_apply_of_not_mem _ _ _ _ _ (by decide)

private theorem omitted_accept (point : List Unit × Sum Unit Bool)
    (image : List Unit × Sum Unit Bool) (moved : unitMove.involution point = image)
    (source : unitDensity point.1 = Dedekind.one)
    (target : unitDensity image.1 = Dedekind.one) :
    involutiveAccept unitMove.involution
        (greenDensity (unitMove.jacobian fun _ => Dedekind.one)
          (splitMergeMass unitDensity fun _ => Dedekind.one))
        point = ENNReal.one := by
  rw [splitMergeKernel_accept (fun _ _ => Dedekind.one_positive), moved, jacobian_one]
  apply metropolisAccept_eq_one
  · show Dedekind.le (Dedekind.mul (unitDensity point.1) Dedekind.one)
      (Dedekind.mul Dedekind.one (Dedekind.mul (unitDensity image.1) Dedekind.one))
    rw [source, target, Dedekind.mul_one, Dedekind.mul_one]
    exact Dedekind.le_refl _
  · show Dedekind.lt Dedekind.zero
      (Dedekind.mul Dedekind.one (Dedekind.mul (unitDensity image.1) Dedekind.one))
    rw [target, Dedekind.mul_one, Dedekind.mul_one]
    exact Dedekind.one_positive

/-- From `[()]` the split is always accepted, so no mass stays. -/
private theorem omitted_from_single :
    omittedKernel [()] (fun values => values = [()]) = ENNReal.zero := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _)]
  unfold omittedKernel splitMergeKernel
  rw [lintegral_involutiveKernel _ _ _ _ _ _ _ (fun _ => Space.discrete_measurable _),
    unitSelection_single, lintegral_dirac _ _ (sum_ennreal _)]
  rw [omitted_accept _ _ (involution_split _ _ _ () ()) rfl rfl, involution_split,
    indicator_other (show ([(), ()] : List Unit) ≠ [()] by decide), indicator_self]
  simp only [ENNReal.sub_self, ENNReal.mul_zero, ENNReal.zero_mul, ENNReal.add_zero]

/-- From `[(), ()]` the marked merge is always accepted, and the unmarked one
stays. -/
private theorem omitted_from_pair :
    omittedKernel [(), ()] (fun values => values = [()]) = halfMass := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _)]
  unfold omittedKernel splitMergeKernel
  rw [lintegral_involutiveKernel _ _ _ _ _ _ _ (fun _ => Space.discrete_measurable _),
    unitSelection_pair, lintegral_fair _ _ _ (sum_ennreal _)]
  rw [omitted_accept _ _ (involution_merge _ _ _ () ()) rfl rfl, involution_merge,
    involution_stay_unmarked, indicator_self,
    indicator_other (show ([(), ()] : List Unit) ≠ [()] by decide)]
  simp only [ENNReal.sub_self, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.mul_one]

/-! ### Scoring only the born element -/

/-- The append move on lists of Booleans. -/
abbrev boolMove : SplitMergeMove (Space.discrete (List Bool)) (Space.discrete Bool)
    (Space.discrete Bool) :=
  move Bool.toNat toNat_injective false

/-- Half on `[false]` and half on `[true, true]`: one element follows the law
at `false`, and a pair's elements follow the law at `true`. -/
@[expose] noncomputable def pairTarget : Measure (Space.discrete (List Bool)) :=
  fair (Space.discrete (List Bool)) [false] [true, true]

/-- Scores only the last element, under the law of its count. Against half the
counting measure the pair target's density is one on `[false]` and
`[true, true]`. This score is one there and also on `[false, true]`. -/
@[expose] noncomputable def lastScore : List Bool → Carrier
  | [false] | [_, true] => Dedekind.one
  | _ => Dedekind.zero

/-- One element splits with probability one half, appending a fair Boolean,
and otherwise takes a merge that its count leaves fixed. Two elements merge. -/
@[expose] noncomputable def pairSplitChoice :
    Measure (Space.sum (Space.discrete Bool) (Space.discrete Bool)) :=
  Measure.smul halfMass
    (Measure.add (fair _ (.inl false) (.inl true)) (Measure.dirac _ (.inr true)))

@[expose] noncomputable def pairSelection :
    Kernel (Space.discrete (List Bool)) (Space.sum (Space.discrete Bool) (Space.discrete Bool)) :=
  Kernel.piecewise (fun values => values.length = 1) (Space.discrete_measurable _)
    (Kernel.const _ pairSplitChoice) (Kernel.const _ (Measure.dirac _ (.inr true)))

@[expose] noncomputable def pairSelectionFinite : Kernel.IsSFinite pairSelection :=
  Kernel.IsSFinite.piecewise
    (Kernel.IsSFinite.const _
      (((Measure.SFinite.ofFinite (fair_probability _ _ _).to_finite).add
        (Measure.SFinite.ofFinite (Measure.IsProbability.dirac _ _).to_finite)).smul
        halfMass trivial))
    (Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite (Measure.IsProbability.dirac _ _).to_finite))
    _ _

/-- The selection's density against counting on both sides: one quarter per
split element and one half on the fixed merge from one element, and one on the
merge from two. -/
@[expose] noncomputable def pairSelectionDensity : List Bool × Sum Bool Bool → Carrier
  | ([_], .inl _) => NNReal.toReal (NNReal.half (NNReal.half NNReal.one))
  | ([_], .inr true) => NNReal.toReal (NNReal.half NNReal.one)
  | ([_, _], .inr true) => Dedekind.one
  | _ => Dedekind.zero

/-- The split/merge kernel whose whole-state density scores only the born
element. -/
@[expose] noncomputable def lastScoreKernel :
    Kernel (Space.discrete (List Bool)) (Space.discrete (List Bool)) :=
  splitMergeKernel pairSelection pairSelectionFinite boolMove lastScore pairSelectionDensity
    (fun _ => Dedekind.one) (fun _ => Space.discrete_measurable _)
    (fun _ => extended_measurable Bool.toNat toNat_injective _)
    (MeasurableMap.constant _ borel Dedekind.one)

private theorem pairSelection_single :
    pairSelection [false] = pairSplitChoice :=
  Kernel.piecewise_apply_of_mem _ _ _ _ _ rfl

private theorem pairSelection_pair :
    pairSelection [true, true] = Measure.dirac _ (.inr true) :=
  Kernel.piecewise_apply_of_not_mem _ _ _ _ _ (by decide)

/-- Splitting `[false]` into `[false, true]` is always accepted: the score
does not see that the first element's law changed. -/
private theorem lastScore_accept :
    involutiveAccept boolMove.involution
        (greenDensity (boolMove.jacobian fun _ => Dedekind.one)
          (splitMergeMass lastScore pairSelectionDensity))
        ([false], .inl true) = ENNReal.one := by
  rw [splitMergeKernel_accept (fun _ _ => Dedekind.one_positive), involution_split,
    jacobian_one]
  apply metropolisAccept_eq_one
  · show Dedekind.le
      (Dedekind.mul Dedekind.one (NNReal.toReal (NNReal.half (NNReal.half NNReal.one))))
      (Dedekind.mul Dedekind.one (Dedekind.mul Dedekind.one Dedekind.one))
    rw [Dedekind.one_mul, Dedekind.one_mul, Dedekind.mul_one]
    exact Dedekind.le_trans (NNReal.half_le _) (NNReal.half_le _)
  · show Dedekind.lt Dedekind.zero
      (Dedekind.mul Dedekind.one (Dedekind.mul Dedekind.one Dedekind.one))
    rw [Dedekind.mul_one, Dedekind.mul_one]
    exact Dedekind.one_positive

/-- From `[false]`, the split that appends `true` lands on `[false, true]`. -/
private theorem lastScore_from_single :
    lastScoreKernel [false] (fun values => values = [false, true]) =
      ENNReal.mul halfMass halfMass := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _)]
  unfold lastScoreKernel splitMergeKernel
  rw [lintegral_involutiveKernel _ _ _ _ _ _ _ (fun _ => Space.discrete_measurable _),
    pairSelection_single, pairSplitChoice, lintegral_smul_measure, lintegral_add_measure,
    lintegral_fair _ _ _ (sum_ennreal _), lintegral_dirac _ _ (sum_ennreal _)]
  rw [lastScore_accept, involution_split, involution_split, involution_stay_single,
    indicator_self, indicator_other (show ([false, false] : List Bool) ≠ [false, true] by decide),
    indicator_other (show ([false] : List Bool) ≠ [false, true] by decide)]
  simp only [ENNReal.sub_self, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.zero_add,
    ENNReal.mul_one]

/-- From `[true, true]`, the merge lands on `[true]` or stays. -/
private theorem lastScore_from_pair :
    lastScoreKernel [true, true] (fun values => values = [false, true]) = ENNReal.zero := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _)]
  unfold lastScoreKernel splitMergeKernel
  rw [lintegral_involutiveKernel _ _ _ _ _ _ _ (fun _ => Space.discrete_measurable _),
    pairSelection_pair, lintegral_dirac _ _ (sum_ennreal _)]
  rw [involution_merge, indicator_other (show ([true] : List Bool) ≠ [false, true] by decide),
    indicator_other (show ([true, true] : List Bool) ≠ [false, true] by decide)]
  simp only [ENNReal.mul_zero, ENNReal.add_zero]

end AppendMove

open AppendMove in
/-- Omitting the merge's selection probability one half from the acceptance
leaves mass one quarter on `[()]` after one step from the unit target, which
puts one half there. -/
theorem omitted_reverse_selection_not_invariant :
    unitTarget.bind omittedKernel (fun values => values = [()]) =
        ENNReal.ofRat (1 / 4) (by decide +kernel) ∧
      unitTarget (fun values => values = [()]) = ENNReal.ofRat (1 / 2) (by decide +kernel) ∧
      ¬ KernelInvariant unitTarget omittedKernel := by
  have stepped : unitTarget.bind omittedKernel (fun values => values = [()]) =
      ENNReal.ofRat (1 / 4) (by decide +kernel) := by
    rw [Measure.bind_apply _ _ (Space.discrete_measurable _), unitTarget,
      Necessity.Weighting.lintegral_fair _ _ _ (fun _ => Space.discrete_measurable _),
      omitted_from_single, omitted_from_pair, ENNReal.zero_add]
    exact Necessity.Weighting.half_ofRat (1 / 2) (1 / 4) _ _ (by decide +kernel)
  have held : unitTarget (fun values => values = [()]) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
    rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _), unitTarget,
      Necessity.Weighting.lintegral_fair _ _ _ (fun _ => Space.discrete_measurable _),
      indicator_self, indicator_other (show ([(), ()] : List Unit) ≠ [()] by decide),
      ENNReal.add_zero, ENNReal.mul_one]
    rfl
  refine ⟨stepped, held, fun invariant => ?_⟩
  unfold KernelInvariant at invariant
  rw [invariant, held] at stepped
  have ordered : ENNReal.le (ENNReal.ofRat (1 / 2) (by decide +kernel))
      (ENNReal.ofRat (1 / 4) (by decide +kernel)) := by
    rw [stepped]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp ordered) (by decide +kernel)

open AppendMove in
/-- A whole-state density that scores only the born element accepts every
split of `[false]` into `[false, true]`. One step from the pair target sends
mass one eighth there, where the target puts none. -/
theorem pair_local_ratio_not_invariant :
    pairTarget.bind lastScoreKernel (fun values => values = [false, true]) =
        ENNReal.ofRat (1 / 8) (by decide +kernel) ∧
      pairTarget (fun values => values = [false, true]) = ENNReal.zero ∧
      ¬ KernelInvariant pairTarget lastScoreKernel := by
  have stepped : pairTarget.bind lastScoreKernel (fun values => values = [false, true]) =
      ENNReal.ofRat (1 / 8) (by decide +kernel) := by
    have quarter : ENNReal.mul Necessity.Weighting.halfMass Necessity.Weighting.halfMass =
        ENNReal.ofRat (1 / 4) (by decide +kernel) :=
      Necessity.Weighting.half_ofRat (1 / 2) (1 / 4) _ _ (by decide +kernel)
    rw [Measure.bind_apply _ _ (Space.discrete_measurable _), pairTarget,
      Necessity.Weighting.lintegral_fair _ _ _ (fun _ => Space.discrete_measurable _),
      lastScore_from_single, lastScore_from_pair, ENNReal.add_zero, quarter]
    exact Necessity.Weighting.half_ofRat (1 / 4) (1 / 8) _ _ (by decide +kernel)
  have held : pairTarget (fun values => values = [false, true]) = ENNReal.zero := by
    rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _), pairTarget,
      Necessity.Weighting.lintegral_fair _ _ _ (fun _ => Space.discrete_measurable _),
      indicator_other (show ([false] : List Bool) ≠ [false, true] by decide),
      indicator_other (show ([true, true] : List Bool) ≠ [false, true] by decide),
      ENNReal.add_zero, ENNReal.mul_zero]
  refine ⟨stepped, held, fun invariant => ?_⟩
  unfold KernelInvariant at invariant
  rw [invariant, held, ← ENNReal.ofRat_zero] at stepped
  have ordered : ENNReal.le (ENNReal.ofRat (1 / 8) (by decide +kernel))
      (ENNReal.ofRat 0 (by decide)) := by
    rw [← stepped]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp ordered) (by decide +kernel)

end
end Problib.Inference
