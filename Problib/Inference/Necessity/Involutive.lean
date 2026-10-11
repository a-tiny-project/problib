module

public import Problib.Inference.Involutive
public import Problib.Inference.Necessity.Weighting
public import Problib.Measure.Space.Countable
set_option autoImplicit false

/-! A trans-dimensional involutive move.

States are either one Boolean or a pair of Booleans. An auxiliary coin splits
`b` into `(b, u)`, or chooses between merging `(b, c)` into `b` and staying. The
target weighs one-Boolean states twice as much as pairs, so the strict test
compares unequal weights across the jump. The step leaves the target invariant
through `reversible_jump_invariant`, with the uniform extended law as the
preserved reference (`splitMerge_invariant`).

Proofs are finite evaluations of Dirac sums. -/

open scoped Problib.Real.AC

namespace Problib.Inference.Necessity.Involutive

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel)
open Problib.Inference.Necessity.Weighting (bools fair halfMass lintegral_fair
  fair_probability)

public section

private theorem bools_ennreal (function : Bool → ENNReal) :
    ENNRealMeasurable bools function :=
  fun _ => Space.discrete_measurable _

/-- A state is one Boolean or a pair of Booleans. -/
abbrev Tagged := Sum Bool (Bool × Bool)

/-- Every set of states is measurable. -/
abbrev tagged : Space Tagged := Space.sum bools (Space.discrete (Bool × Bool))

/-- A state with its auxiliary coin. -/
abbrev extended : Space (Tagged × Bool) := Space.product tagged bools

private def codeBool (value : Bool) : Nat := if value then 1 else 0

private def code : Tagged × Bool → Nat
  | (.inl first, coin) => 2 * codeBool first + codeBool coin
  | (.inr (first, second), coin) =>
      4 + 4 * codeBool first + 2 * codeBool second + codeBool coin

private def decode : Nat → Tagged × Bool
  | 0 => (.inl false, false)
  | 1 => (.inl false, true)
  | 2 => (.inl true, false)
  | 3 => (.inl true, true)
  | 4 => (.inr (false, false), false)
  | 5 => (.inr (false, false), true)
  | 6 => (.inr (false, true), false)
  | 7 => (.inr (false, true), true)
  | 8 => (.inr (true, false), false)
  | 9 => (.inr (true, false), true)
  | 10 => (.inr (true, true), false)
  | _ => (.inr (true, true), true)

private theorem decode_code (point : Tagged × Bool) : decode (code point) = point := by
  rcases point with ⟨(first | ⟨first, second⟩), coin⟩ <;>
    cases first <;> (try cases second) <;> cases coin <;> rfl

/-- Every set of extended states is measurable: each is a countable union of
measurable points. -/
theorem extended_measurable (set : Set (Tagged × Bool)) : extended.Measurable set := by
  have points := Space.i_union_of_nat_injection extended code
    (fun left right same => by
      rw [← decode_code left, ← decode_code right, same])
    (fun point => Set.product (fun state => set point ∧ state = point.1)
      (fun coin => coin = point.2))
    (fun _ => Space.product_set_measurable tagged bools
      ⟨Space.discrete_measurable _, Space.discrete_measurable _⟩
      (Space.discrete_measurable _))
  have same : (fun value => ∃ point, Set.product
      (fun state => set point ∧ state = point.1)
      (fun coin => coin = point.2) value) = set := by
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

private theorem extended_ennreal (function : Tagged × Bool → ENNReal) :
    ENNRealMeasurable extended function :=
  fun _ => extended_measurable _

/-- Split `b` into `(b, u)`, merge `(b, c)` into `b` on a `false` coin, and
stay on a `true` coin. -/
@[expose] def splitMerge : Tagged × Bool → Tagged × Bool
  | (.inl first, coin) => (.inr (first, coin), false)
  | (.inr (first, second), false) => (.inl first, second)
  | (.inr (first, second), true) => (.inr (first, second), true)

theorem splitMerge_measurable : MeasurableMap extended extended splitMerge :=
  fun _ => extended_measurable _

theorem splitMerge_involutive (point : Tagged × Bool) :
    splitMerge (splitMerge point) = point := by
  rcases point with ⟨(first | ⟨first, second⟩), coin⟩ <;>
    (try cases coin) <;> rfl

/-- One unit of mass on each state. -/
@[expose] noncomputable def stateCount : Measure tagged :=
  Measure.add
    (Measure.add (Measure.dirac tagged (.inl false)) (Measure.dirac tagged (.inl true)))
    (Measure.add
      (Measure.add (Measure.dirac tagged (.inr (false, false)))
        (Measure.dirac tagged (.inr (false, true))))
      (Measure.add (Measure.dirac tagged (.inr (true, false)))
        (Measure.dirac tagged (.inr (true, true)))))

/-- The auxiliary coin ignores the state. -/
@[expose] noncomputable def coinKernel : Kernel tagged bools :=
  Kernel.const tagged (fair bools false true)

@[expose] noncomputable def coinKernelSFinite : Kernel.IsSFinite coinKernel :=
  Kernel.IsSFinite.const tagged
    (Measure.SFinite.ofFinite (fair_probability bools false true).to_finite)

/-- The uniform extended law: each state beside a fair coin. -/
@[expose] noncomputable def uniformExtended : Measure extended :=
  stateCount.semiproduct coinKernel coinKernelSFinite

private theorem lintegral_uniformExtended (function : Tagged × Bool → ENNReal) :
    lintegral uniformExtended function =
      ENNReal.add
        (ENNReal.add
          (ENNReal.mul halfMass
            (ENNReal.add (function (.inl false, false)) (function (.inl false, true))))
          (ENNReal.mul halfMass
            (ENNReal.add (function (.inl true, false)) (function (.inl true, true)))))
        (ENNReal.add
          (ENNReal.add
            (ENNReal.mul halfMass
              (ENNReal.add (function (.inr (false, false), false))
                (function (.inr (false, false), true))))
            (ENNReal.mul halfMass
              (ENNReal.add (function (.inr (false, true), false))
                (function (.inr (false, true), true)))))
          (ENNReal.add
            (ENNReal.mul halfMass
              (ENNReal.add (function (.inr (true, false), false))
                (function (.inr (true, false), true))))
            (ENNReal.mul halfMass
              (ENNReal.add (function (.inr (true, true), false))
                (function (.inr (true, true), true)))))) := by
  have inner : ∀ state : Tagged,
      ENNRealMeasurable bools (fun coin => function (state, coin)) :=
    fun _ => bools_ennreal _
  have outer : ENNRealMeasurable tagged
      (fun state => lintegral (coinKernel state) (fun coin => function (state, coin))) :=
    fun _ => ⟨Space.discrete_measurable _, Space.discrete_measurable _⟩
  unfold uniformExtended stateCount
  rw [lintegral_semiproduct _ _ _ (extended_ennreal function)]
  simp only [lintegral_add_measure]
  rw [lintegral_dirac _ _ outer, lintegral_dirac _ _ outer, lintegral_dirac _ _ outer,
    lintegral_dirac _ _ outer, lintegral_dirac _ _ outer, lintegral_dirac _ _ outer]
  simp only [coinKernel, Kernel.const_apply]
  rw [lintegral_fair _ _ _ (inner _), lintegral_fair _ _ _ (inner _),
    lintegral_fair _ _ _ (inner _), lintegral_fair _ _ _ (inner _),
    lintegral_fair _ _ _ (inner _), lintegral_fair _ _ _ (inner _)]

/-- The split/merge involution preserves the uniform extended law. -/
theorem uniformExtended_invariant :
    uniformExtended.map splitMerge splitMerge_measurable = uniformExtended := by
  apply Measure.ext
  intro set setMeasurable
  rw [apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_map _ _ _ (extended_ennreal _),
    lintegral_uniformExtended, lintegral_uniformExtended]
  simp only [splitMerge, ENNReal.mul_add]
  ac_rfl

/-- Weight two on a single Boolean and one on a pair. -/
@[expose] noncomputable def stateWeight : Tagged → Carrier
  | .inl _ => Dedekind.add Dedekind.one Dedekind.one
  | .inr _ => Dedekind.one

/-- The weighted target on states. -/
@[expose] noncomputable def splitTarget : Measure tagged :=
  stateCount.withDensity (fun state => ENNReal.ofReal (stateWeight state))

/-- The weight of an extended state's state. -/
@[expose] noncomputable def splitFlux (point : Tagged × Bool) : Carrier :=
  stateWeight point.1

theorem splitFlux_measurable : MeasurableMap extended borel splitFlux :=
  fun _ => extended_measurable _

/-- The split/merge step with the strict test leaves the weighted target
invariant. -/
theorem splitMerge_invariant :
    KernelInvariant splitTarget
      (involutiveKernel coinKernel coinKernelSFinite splitMerge splitMerge_measurable
        (involutiveAccept splitMerge splitFlux)
        (involutiveAccept_measurable splitMerge splitMerge_measurable
          splitFlux_measurable)) :=
  reversible_jump_invariant splitTarget coinKernel coinKernelSFinite
    (fun _ => fair_probability bools false true)
    splitMerge splitMerge_measurable splitMerge_involutive
    uniformExtended uniformExtended_invariant splitFlux_measurable
    (Measure.semiproduct_withDensity_left stateCount
      (fun _ => ⟨Space.discrete_measurable _, Space.discrete_measurable _⟩)
      coinKernel coinKernelSFinite)

end

end Problib.Inference.Necessity.Involutive
