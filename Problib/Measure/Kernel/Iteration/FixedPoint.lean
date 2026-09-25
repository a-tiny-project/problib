module

public import Problib.Measure.Kernel.Supremum
public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Kernel.Sum

set_option autoImplicit false

/-! Least fixed points of monotone, countably continuous kernel operators. -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

universe w x
variable {gamma : Type w} {delta : Type x}
  {otherSource : Space gamma} {otherTarget : Space delta}
universe y
variable {epsilon : Type y} {middle : Space epsilon}

/-- Attaching an input coordinate preserves kernel order with any two
constructive s-finite witnesses. -/
public theorem attach_le {first second : Kernel source target}
    (firstFinite : IsSFinite first) (secondFinite : IsSFinite second)
    (included : le first second) :
    le (Kernel.attach first firstFinite) (Kernel.attach second secondFinite) := by
  intro input set measurable
  rw [Kernel.attach_apply, Kernel.attach_apply]
  exact Measure.map_le_map (included input)
    (fun value => (input, value)) (pair_left_measurable input) set

/-- Attaching a kernel depends on its measure, not the chosen decomposition. -/
public theorem attach_congr_kernel {first second : Kernel source target}
    (firstFinite : IsSFinite first) (secondFinite : IsSFinite second)
    (same : first = second) :
    Kernel.attach first firstFinite = Kernel.attach second secondFinite := by
  apply Kernel.ext
  intro input
  rw [Kernel.attach_apply, Kernel.attach_apply, same]

/-- Attaching commutes with finite cumulative sums. -/
public theorem attach_prefixSum
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index)) (count : Nat) :
    Kernel.attach (Kernel.prefixSum increments count)
        (IsSFinite.prefixSumFinite increments finite count) =
      Kernel.prefixSum
        (fun index => Kernel.attach (increments index) (finite index))
        count := by
  induction count with
  | zero =>
      change Kernel.attach (Kernel.zero source target) _ =
        Kernel.zero source (Space.product source target)
      exact attach_zero _
  | succ count induction =>
      change Kernel.attach
          (Kernel.add (Kernel.prefixSum increments count) (increments count)) _ =
        Kernel.add
          (Kernel.prefixSum
            (fun index => Kernel.attach (increments index) (finite index))
            count)
          (Kernel.attach (increments count) (finite count))
      rw [attach_add _ _ (IsSFinite.prefixSumFinite increments finite count)
        (finite count) _, induction]

/-- A constructive s-finite witness for a chain limit also permits the
attached coordinate to commute with that limit. -/
public theorem attach_iSupIncreasing
    (kernels : Nat → Kernel source target)
    (increasing : ∀ index, le (kernels index) (kernels (index + 1)))
    (finite : ∀ index, IsSFinite (kernels index))
    (limitFinite : IsSFinite (iSupIncreasing kernels increasing)) :
    Kernel.attach (iSupIncreasing kernels increasing) limitFinite =
      iSupIncreasing (fun index => Kernel.attach (kernels index) (finite index))
        (fun index => attach_le (finite index) (finite (index + 1))
          (increasing index)) := by
  apply Kernel.ext_measurable
  intro input set measurable
  rw [Kernel.attach_apply,
    (iSupIncreasing kernels increasing input).map_apply
      (fun value => (input, value)) (pair_left_measurable input) measurable,
    iSupIncreasing_apply_measurable kernels increasing input
      (pair_left_measurable input measurable),
    iSupIncreasing_apply_measurable _ _ input measurable]
  apply congrArg ENNReal.iSup
  funext index
  rw [Kernel.attach_apply,
    (kernels index input).map_apply
      (fun value => (input, value)) (pair_left_measurable input) measurable]

/-- Source precomposition preserves kernel order. -/
public theorem precomp_le {first second : Kernel source target}
    (function : gamma → alpha)
    (measurable : MeasurableMap otherSource source function)
    (included : le first second) :
    le (first.precomp function measurable) (second.precomp function measurable) := by
  intro input set setMeasurable
  exact included (function input) set setMeasurable

/-- Source precomposition commutes with increasing kernel limits. -/
public theorem precomp_iSupIncreasing
    (kernels : Nat → Kernel source target)
    (increasing : ∀ index, le (kernels index) (kernels (index + 1)))
    (function : gamma → alpha)
    (measurable : MeasurableMap otherSource source function) :
    (iSupIncreasing kernels increasing).precomp function measurable =
      iSupIncreasing (fun index => (kernels index).precomp function measurable)
        (fun index => precomp_le function measurable (increasing index)) := by
  apply Kernel.ext
  intro input
  rw [Kernel.precomp_apply, iSupIncreasing_apply, iSupIncreasing_apply]
  rfl

/-- Source precomposition commutes with each cumulative prefix. -/
public theorem precomp_prefixSum
    (increments : Nat → Kernel source target) (count : Nat)
    (function : gamma → alpha)
    (measurable : MeasurableMap otherSource source function) :
    (prefixSum increments count).precomp function measurable =
      prefixSum (fun index => (increments index).precomp function measurable) count := by
  induction count with
  | zero =>
      apply Kernel.ext
      intro input
      rfl
  | succ count induction =>
      apply Kernel.ext
      intro input
      exact congrArg
        (fun measure : Measure target => Measure.add measure (increments count (function input)))
        (congrArg (fun kernel : Kernel otherSource target => kernel input) induction)

/-- Copairing commutes with cumulative sums on both branches. -/
public theorem copair_prefixSum
    (first : Nat → Kernel source target)
    (second : Nat → Kernel otherSource target) (count : Nat) :
    Kernel.copair (prefixSum first count) (prefixSum second count) =
      prefixSum (fun index => Kernel.copair (first index) (second index)) count := by
  apply Kernel.sum_ext
  · intro input
    induction count with
    | zero => rfl
    | succ count induction =>
        have prior : prefixSum first count input =
            prefixSum (fun index => Kernel.copair (first index) (second index)) count
              (Sum.inl input) := induction
        change Measure.add (prefixSum first count input) (first count input) =
          Measure.add
            (prefixSum (fun index => Kernel.copair (first index) (second index)) count
              (Sum.inl input))
            (first count input)
        rw [prior]
  · intro input
    induction count with
    | zero => rfl
    | succ count induction =>
        have prior : prefixSum second count input =
            prefixSum (fun index => Kernel.copair (first index) (second index)) count
              (Sum.inr input) := induction
        change Measure.add (prefixSum second count input) (second count input) =
          Measure.add
            (prefixSum (fun index => Kernel.copair (first index) (second index)) count
              (Sum.inr input))
            (second count input)
        rw [prior]

/-- An operator that preserves the supremum of every increasing kernel chain. -/
public structure OmegaContinuous
    (operator : Kernel source target → Kernel source target) : Prop where
  monotone : ∀ {left right}, le left right → le (operator left) (operator right)
  continuous : ∀ (kernels : Nat → Kernel source target)
      (increasing : ∀ index, le (kernels index) (kernels (index + 1))),
    operator (iSupIncreasing kernels increasing) =
      iSupIncreasing (fun index => operator (kernels index))
        (fun index => monotone (increasing index))

/-- Exiting now or taking one step is continuous in the continuation kernel. -/
public theorem OmegaContinuous.linear (step : Kernel source source)
    (exit : Kernel source target) :
    OmegaContinuous (fun continuation => Kernel.add exit (step.comp continuation)) := by
  refine ⟨?_, ?_⟩
  · intro left right included
    exact add_le_add (le_refl exit) (comp_le_comp_right step included)
  · intro kernels increasing
    rw [comp_iSupIncreasing_right step kernels increasing]
    exact add_iSupIncreasing exit
      (fun index => step.comp (kernels index))
      (fun index => comp_le_comp_right step (increasing index))

/-- Apply an operator a finite number of times, beginning at the zero kernel. -/
@[expose] public noncomputable def fixedPointApproximant
    (operator : Kernel source target → Kernel source target) :
    Nat → Kernel source target
  | 0 => Kernel.zero source target
  | count + 1 => operator (fixedPointApproximant operator count)

/-- Each additional unfolding adds to a positive operator's approximant. -/
public theorem fixedPointApproximant_monotone
    (operator : Kernel source target → Kernel source target)
    (monotone : ∀ {left right}, le left right → le (operator left) (operator right))
    (count : Nat) :
    le (fixedPointApproximant operator count)
      (fixedPointApproximant operator (count + 1)) := by
  induction count with
  | zero => exact zero_le _
  | succ count induction => exact monotone induction

/-- The supremum of the finite zero-based unfoldings. -/
@[expose] public noncomputable def leastFixedPoint
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) : Kernel source target :=
  iSupIncreasing (fixedPointApproximant operator)
    (fixedPointApproximant_monotone operator continuous.monotone)

/-- The least fixed point evaluates as the supremum of finite unfoldings. -/
public theorem leastFixedPoint_apply_measurable
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) (input : alpha)
    {set : Set beta} (measurable : target.Measurable set) :
    leastFixedPoint operator continuous input set =
      ENNReal.iSup (fun count => fixedPointApproximant operator count input set) :=
  iSupIncreasing_apply_measurable _ _ input measurable

/-- The supremum satisfies its one-step unfolding equation. -/
public theorem leastFixedPoint_unfold
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) :
    operator (leastFixedPoint operator continuous) =
      leastFixedPoint operator continuous := by
  let approximants := fixedPointApproximant operator
  let increasing := fixedPointApproximant_monotone operator continuous.monotone
  change operator (iSupIncreasing approximants increasing) =
    iSupIncreasing approximants increasing
  rw [continuous.continuous approximants increasing]
  apply le_antisymm
  · apply iSupIncreasing_le
    intro count
    exact le_iSupIncreasing approximants increasing (count + 1)
  · apply iSupIncreasing_le
    intro count
    cases count with
    | zero => exact zero_le _
    | succ count =>
        exact le_iSupIncreasing (fun index => operator (approximants index))
          (fun index => continuous.monotone (increasing index)) count

/-- Every pre-fixed point bounds the supremum of the zero-based unfoldings. -/
public theorem leastFixedPoint_least
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator)
    (candidate : Kernel source target)
    (prefixed : le (operator candidate) candidate) :
    le (leastFixedPoint operator continuous) candidate := by
  apply iSupIncreasing_le
  intro count
  induction count with
  | zero => exact zero_le candidate
  | succ count induction =>
      exact le_trans (continuous.monotone induction) prefixed

/-- The countable exit-path loop is the least fixed point of its linear
continuation operator. -/
public theorem leastFixedPoint_linear_eq_loop (step : Kernel source source)
    (exit : Kernel source target) :
    leastFixedPoint (fun continuation => Kernel.add exit (step.comp continuation))
      (OmegaContinuous.linear step exit) = loop step exit := by
  apply le_antisymm
  · apply leastFixedPoint_least
    rw [← loop_unfold step exit]
    exact le_refl _
  · apply loop_least
    rw [leastFixedPoint_unfold
      (fun continuation => Kernel.add exit (step.comp continuation))
      (OmegaContinuous.linear step exit)]
    exact le_refl _

/-- An operator whose finite unfoldings are cumulative s-finite increments
has an s-finite least fixed point. The increment presentation is essential:
monotonicity alone supplies no constructive decomposition. -/
public noncomputable def IsSFinite.leastFixedPointOfPrefixSum
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      fixedPointApproximant operator index = prefixSum increments index) :
    IsSFinite (leastFixedPoint operator continuous) :=
  IsSFinite.ofPrefixSum
    (fixedPointApproximant operator)
    (fixedPointApproximant_monotone operator continuous.monotone)
    increments finite prefix_eq

/-! ### Fixed points whose operator requires an s-finite input -/

/-- A kernel together with the constructive decomposition required by
operations such as attaching its output to its input. -/
public structure SFiniteKernel (source : Space alpha) (target : Space beta) where
  kernel : Kernel source target
  sfinite : IsSFinite kernel

/-- Monotonicity is independent of the decomposition supplied for either
kernel. Continuity is required along chains with cumulative increments, which
are exactly the chains whose supremum has a constructive s-finite witness. -/
public structure PrefixContinuous
    (operator : SFiniteKernel source target → SFiniteKernel source target) : Prop where
  monotone : ∀ (first second : SFiniteKernel source target),
    le first.kernel second.kernel → le (operator first).kernel (operator second).kernel
  continuous : ∀ (chain : Nat → SFiniteKernel source target)
      (increasing : ∀ index, le (chain index).kernel (chain (index + 1)).kernel)
      (increments : Nat → Kernel source target)
      (finite : ∀ index, IsSFinite (increments index))
      (prefix_eq : ∀ index, (chain index).kernel = prefixSum increments index),
    (operator ⟨iSupIncreasing (fun index => (chain index).kernel) increasing,
      IsSFinite.ofPrefixSum (fun index => (chain index).kernel) increasing
        increments finite prefix_eq⟩).kernel =
      iSupIncreasing (fun index => (operator (chain index)).kernel)
        (fun index => monotone (chain index) (chain (index + 1)) (increasing index))

/-- A monotone witnessed operator gives the same answer for every s-finite
decomposition of one kernel. -/
public theorem PrefixContinuous.witness_independent
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator) (kernel : Kernel source target)
    (first second : IsSFinite kernel) :
    (operator ⟨kernel, first⟩).kernel = (operator ⟨kernel, second⟩).kernel :=
  le_antisymm
    (continuous.monotone _ _ (le_refl kernel))
    (continuous.monotone _ _ (le_refl kernel))

/-- Equal input kernels give equal outputs regardless of their witnesses. -/
public theorem PrefixContinuous.congr_kernel
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (first second : SFiniteKernel source target)
    (equal : first.kernel = second.kernel) :
    (operator first).kernel = (operator second).kernel :=
  le_antisymm
    (continuous.monotone first second (equal ▸ le_refl second.kernel))
    (continuous.monotone second first (equal.symm ▸ le_refl first.kernel))

/-- The zero increment has a constructive s-finite witness. -/
@[expose] public noncomputable def SFiniteKernel.zero
    (source : Space alpha) (target : Space beta) : SFiniteKernel source target :=
  ⟨Kernel.zero source target, IsSFinite.zero source target⟩

/-- A finite prefix of witnessed increments. -/
@[expose] public noncomputable def SFiniteKernel.prefixSum
    (increments : Nat → SFiniteKernel source target) (count : Nat) :
    SFiniteKernel source target :=
  ⟨Kernel.prefixSum (fun index => (increments index).kernel) count,
    IsSFinite.prefixSumFinite (fun index => (increments index).kernel)
      (fun index => (increments index).sfinite) count⟩

/-- The witnessed one-step operator for exit paths and a fixed step kernel. -/
@[expose] public noncomputable def SFiniteKernel.linear
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit)
    (continuation : SFiniteKernel source target) : SFiniteKernel source target :=
  ⟨Kernel.add exit (step.comp continuation.kernel),
    IsSFinite.add exitFinite (IsSFinite.comp stepFinite continuation.sfinite)⟩

/-- The witnessed linear operator respects order across arbitrary witnesses. -/
public theorem SFiniteKernel.linear_monotone
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit)
    (first second : SFiniteKernel source target)
    (included : le first.kernel second.kernel) :
    le (SFiniteKernel.linear step stepFinite exit exitFinite first).kernel
      (SFiniteKernel.linear step stepFinite exit exitFinite second).kernel :=
  add_le_add (le_refl exit) (comp_le_comp_right step included)

/-- The witnessed linear operator is continuous on cumulative-prefix chains. -/
public theorem PrefixContinuous.linear
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit) :
    PrefixContinuous (SFiniteKernel.linear step stepFinite exit exitFinite) := by
  refine ⟨SFiniteKernel.linear_monotone step stepFinite exit exitFinite, ?_⟩
  intro chain increasing increments finite prefix_eq
  change Kernel.add exit (step.comp
    (iSupIncreasing (fun index => (chain index).kernel) increasing)) = _
  rw [comp_iSupIncreasing_right step (fun index => (chain index).kernel) increasing]
  exact add_iSupIncreasing exit
    (fun index => step.comp (chain index).kernel)
    (fun index => comp_le_comp_right step (increasing index))

/-- A positive operator gives the increment first completed at each output
depth from the input increments at smaller depths. Its prefix equation is the
constructive path decomposition of one body application. -/
public structure CausalPrefixOperator
    (operator : SFiniteKernel source target → SFiniteKernel source target) where
  action : (Nat → SFiniteKernel source target) → Nat → SFiniteKernel source target
  causal : ∀ (first second : Nat → SFiniteKernel source target) (count : Nat),
    (∀ index, index < count → (first index).kernel = (second index).kernel) →
      (action first count).kernel = (action second count).kernel
  prefix_eq : ∀ (increments : Nat → SFiniteKernel source target) (count : Nat),
    (operator (SFiniteKernel.prefixSum increments count)).kernel =
      Kernel.prefixSum (fun index => (action increments index).kernel) (count + 1)

/-- A positive kernel expression over a witnessed continuation. Its output
spaces may differ from the continuation spaces, as they do inside a bind. -/
public structure CausalPrefixMap (source : Space alpha) (target : Space beta)
    (otherSource : Space gamma) (otherTarget : Space delta) where
  operator : SFiniteKernel source target → SFiniteKernel otherSource otherTarget
  monotone : ∀ first second, le first.kernel second.kernel →
    le (operator first).kernel (operator second).kernel
  continuous : ∀ (chain : Nat → SFiniteKernel source target)
      (increasing : ∀ index, le (chain index).kernel (chain (index + 1)).kernel)
      (increments : Nat → Kernel source target)
      (finite : ∀ index, IsSFinite (increments index))
      (prefix_eq : ∀ index, (chain index).kernel = prefixSum increments index),
    (operator ⟨iSupIncreasing (fun index => (chain index).kernel) increasing,
      IsSFinite.ofPrefixSum (fun index => (chain index).kernel) increasing
        increments finite prefix_eq⟩).kernel =
      iSupIncreasing (fun index => (operator (chain index)).kernel)
        (fun index => monotone _ _ (increasing index))
  action : (Nat → SFiniteKernel source target) → Nat →
    SFiniteKernel otherSource otherTarget
  causal : ∀ (first second : Nat → SFiniteKernel source target) (count : Nat),
    (∀ index, index < count → (first index).kernel = (second index).kernel) →
      (action first count).kernel = (action second count).kernel
  prefix_eq : ∀ (increments : Nat → SFiniteKernel source target) (count : Nat),
    (operator (SFiniteKernel.prefixSum increments count)).kernel =
      prefixSum (fun index => (action increments index).kernel) (count + 1)

/-- A map from a continuation space back to itself is a witnessed fixed-point
operator with the same causal path action. -/
public def CausalPrefixMap.toOperator
    (expression : CausalPrefixMap source target source target) :
    CausalPrefixOperator expression.operator where
  action := expression.action
  causal := expression.causal
  prefix_eq := expression.prefix_eq

/-- The order and continuity certificate of a positive expression. -/
public def CausalPrefixMap.toContinuous
    (expression : CausalPrefixMap source target source target) :
    PrefixContinuous expression.operator where
  monotone := expression.monotone
  continuous := expression.continuous

/-- An independent body contributes its kernel at depth zero and no further
increments. -/
public noncomputable def CausalPrefixMap.constant
    (source : Space alpha) (target : Space beta)
    (fixed : SFiniteKernel otherSource otherTarget) :
    CausalPrefixMap source target otherSource otherTarget where
  operator := fun _ => fixed
  monotone := by intro _ _ _; exact le_refl fixed.kernel
  continuous := by
    intro chain increasing increments finite prefix_eq
    apply le_antisymm
    · exact le_iSupIncreasing (fun _ => fixed.kernel)
        (fun _ => le_refl fixed.kernel) 0
    · apply iSupIncreasing_le
      intro _
      exact le_refl fixed.kernel
  action := fun _ count =>
    if count = 0 then fixed else SFiniteKernel.zero otherSource otherTarget
  causal := by intro _ _ _ _; rfl
  prefix_eq := by
    intro increments count
    induction count with
    | zero =>
        change fixed.kernel = Kernel.add (Kernel.zero otherSource otherTarget) fixed.kernel
        rw [zero_add]
    | succ count induction =>
        change fixed.kernel = Kernel.add
          (Kernel.prefixSum
            (fun index => (if index = 0 then fixed
              else SFiniteKernel.zero otherSource otherTarget).kernel) (count + 1))
          (Kernel.zero otherSource otherTarget)
        rw [add_zero]
        exact induction

/-- Reading the continuation itself shifts its path increments by one output
depth, leaving the zero-depth increment empty. -/
public noncomputable def CausalPrefixMap.identity
    (source : Space alpha) (target : Space beta) :
    CausalPrefixMap source target source target where
  operator := id
  monotone := by intro _ _ included; exact included
  continuous := by intro _ _ _ _ _; rfl
  action := fun increments count =>
    match count with
    | 0 => SFiniteKernel.zero source target
    | index + 1 => increments index
  causal := by
    intro first second count equal
    cases count with
    | zero => rfl
    | succ count => exact equal count (Nat.lt_succ_self count)
  prefix_eq := by
    intro increments count
    induction count with
    | zero =>
        change Kernel.zero source target =
          Kernel.add (Kernel.zero source target) (Kernel.zero source target)
        rw [zero_add]
    | succ count induction =>
        have prior : Kernel.prefixSum (fun index => (increments index).kernel) count =
            Kernel.prefixSum (fun index =>
              (match index with
                | 0 => SFiniteKernel.zero source target
                | step + 1 => increments step).kernel) (count + 1) := induction
        change Kernel.add (Kernel.prefixSum (fun index => (increments index).kernel) count)
            (increments count).kernel =
          Kernel.add
            (Kernel.prefixSum (fun index =>
              (match index with
                | 0 => SFiniteKernel.zero source target
                | step + 1 => increments step).kernel) (count + 1))
            (increments count).kernel
        rw [prior]

/-- Bind two positive kernel expressions, allowing the continuation to be
used more than once. Diagonal path increments count every pair of paths whose
maximum depth has just been completed. -/
public noncomputable def CausalPrefixMap.compose
    (first : CausalPrefixMap source target otherSource middle)
    (second : CausalPrefixMap source target middle otherTarget) :
    CausalPrefixMap source target otherSource otherTarget where
  operator := fun continuation =>
    ⟨(first.operator continuation).kernel.comp (second.operator continuation).kernel,
      IsSFinite.comp (first.operator continuation).sfinite
        (second.operator continuation).sfinite⟩
  monotone := by
    intro left right included
    exact le_trans
      (comp_le_comp_left (first.monotone left right included)
        (second.operator left).kernel)
      (comp_le_comp_right (first.operator right).kernel
        (second.monotone left right included))
  continuous := by
    intro chain increasing increments finite prefix_eq
    change (first.operator ⟨_, _⟩).kernel.comp
      (second.operator ⟨_, _⟩).kernel = _
    rw [first.continuous chain increasing increments finite prefix_eq,
      second.continuous chain increasing increments finite prefix_eq]
    exact comp_iSupIncreasing_diagonal
      (fun index => (first.operator (chain index)).kernel)
      (fun index => first.monotone _ _ (increasing index))
      (fun index => (second.operator (chain index)).kernel)
      (fun index => second.monotone _ _ (increasing index))
  action := fun increments count =>
    ⟨diagonalPrefixIncrement
        (fun index => (first.action increments index).kernel)
        (fun index => (second.action increments index).kernel) count,
      IsSFinite.diagonalPrefixIncrement
        (fun index => (first.action increments index).kernel)
        (fun index => (second.action increments index).kernel)
        (fun index => (first.action increments index).sfinite)
        (fun index => (second.action increments index).sfinite) count⟩
  causal := by
    intro left right count equal
    change diagonalPrefixIncrement
      (fun index => (first.action left index).kernel)
      (fun index => (second.action left index).kernel) count =
      diagonalPrefixIncrement
        (fun index => (first.action right index).kernel)
        (fun index => (second.action right index).kernel) count
    unfold diagonalPrefixIncrement
    have firstPrefix := prefixSum_congr count (fun index earlier =>
      first.causal left right index
        (fun step smaller => equal step (Nat.lt_trans smaller earlier)))
    have secondPrefix := prefixSum_congr (count + 1) (fun index earlier =>
      second.causal left right index
        (fun step smaller => equal step
          (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ earlier))))
    rw [firstPrefix, secondPrefix]
    change Kernel.add
        ((Kernel.prefixSum (fun index => (first.action right index).kernel) count).comp
          (second.action left count).kernel)
        ((first.action left count).kernel.comp
          (Kernel.prefixSum (fun index => (second.action right index).kernel) (count + 1))) =
      Kernel.add
        ((Kernel.prefixSum (fun index => (first.action right index).kernel) count).comp
          (second.action right count).kernel)
        ((first.action right count).kernel.comp
          (Kernel.prefixSum (fun index => (second.action right index).kernel) (count + 1)))
    rw [first.causal left right count equal,
      second.causal left right count equal]
  prefix_eq := by
    intro increments count
    change (first.operator (SFiniteKernel.prefixSum increments count)).kernel.comp
      (second.operator (SFiniteKernel.prefixSum increments count)).kernel = _
    rw [first.prefix_eq increments count, second.prefix_eq increments count,
      comp_prefixSum_eq_prefixSum_diagonalPrefixIncrement]

/-- Keep the source coordinate alongside each output of a positive kernel
expression. Its s-finite witness is carried through every finite prefix. -/
public noncomputable def CausalPrefixMap.attach
    (expression : CausalPrefixMap source target otherSource otherTarget) :
    CausalPrefixMap source target otherSource
      (Space.product otherSource otherTarget) where
  operator := fun continuation =>
    ⟨Kernel.attach (expression.operator continuation).kernel
        (expression.operator continuation).sfinite,
      (expression.operator continuation).sfinite.attach⟩
  monotone := by
    intro first second included
    exact attach_le (expression.operator first).sfinite
      (expression.operator second).sfinite
      (expression.monotone first second included)
  continuous := by
    intro chain increasing increments finite prefix_eq
    let limit : SFiniteKernel source target :=
      ⟨iSupIncreasing (fun index => (chain index).kernel) increasing,
        IsSFinite.ofPrefixSum (fun index => (chain index).kernel) increasing
          increments finite prefix_eq⟩
    let outputs := fun index => (expression.operator (chain index)).kernel
    let outputIncreasing := fun index =>
      expression.monotone (chain index) (chain (index + 1)) (increasing index)
    have same : (expression.operator limit).kernel =
        iSupIncreasing outputs outputIncreasing :=
      expression.continuous chain increasing increments finite prefix_eq
    let outputFinite : IsSFinite (iSupIncreasing outputs outputIncreasing) :=
      same ▸ (expression.operator limit).sfinite
    exact (attach_congr_kernel (expression.operator limit).sfinite outputFinite same).trans
      (attach_iSupIncreasing outputs outputIncreasing
        (fun index => (expression.operator (chain index)).sfinite) outputFinite)
  action := fun increments count =>
    ⟨Kernel.attach (expression.action increments count).kernel
        (expression.action increments count).sfinite,
      (expression.action increments count).sfinite.attach⟩
  causal := by
    intro first second count equal
    exact attach_congr_kernel
      (expression.action first count).sfinite
      (expression.action second count).sfinite
      (expression.causal first second count equal)
  prefix_eq := by
    intro increments count
    let paths := fun index => (expression.action increments index).kernel
    let finite := fun index => (expression.action increments index).sfinite
    have same : (expression.operator (SFiniteKernel.prefixSum increments count)).kernel =
        Kernel.prefixSum paths (count + 1) := expression.prefix_eq increments count
    calc
      Kernel.attach (expression.operator (SFiniteKernel.prefixSum increments count)).kernel
          (expression.operator (SFiniteKernel.prefixSum increments count)).sfinite =
        Kernel.attach (Kernel.prefixSum paths (count + 1))
          (IsSFinite.prefixSumFinite paths finite (count + 1)) :=
        attach_congr_kernel _ _ same
      _ = Kernel.prefixSum
          (fun index => Kernel.attach (paths index) (finite index)) (count + 1) :=
        attach_prefixSum paths finite (count + 1)

/-- Apply a measurable output map to every path of a positive expression. -/
public noncomputable def CausalPrefixMap.map
    (expression : CausalPrefixMap source target otherSource middle)
    (function : epsilon → delta)
    (measurable : MeasurableMap middle otherTarget function) :
    CausalPrefixMap source target otherSource otherTarget where
  operator := fun continuation =>
    ⟨(expression.operator continuation).kernel.map function measurable,
      (expression.operator continuation).sfinite.map function measurable⟩
  monotone := by
    intro first second included
    exact map_le function measurable (expression.monotone first second included)
  continuous := by
    intro chain increasing increments finite prefix_eq
    change (expression.operator ⟨_, _⟩).kernel.map function measurable = _
    rw [expression.continuous chain increasing increments finite prefix_eq]
    exact map_iSupIncreasing
      (fun index => (expression.operator (chain index)).kernel)
      (fun index => expression.monotone _ _ (increasing index)) function measurable
  action := fun increments count =>
    ⟨(expression.action increments count).kernel.map function measurable,
      (expression.action increments count).sfinite.map function measurable⟩
  causal := by
    intro first second count equal
    exact congrArg (fun kernel : Kernel otherSource middle =>
      kernel.map function measurable) (expression.causal first second count equal)
  prefix_eq := by
    intro increments count
    change (expression.operator (SFiniteKernel.prefixSum increments count)).kernel.map
      function measurable = _
    rw [expression.prefix_eq increments count]
    exact map_prefixSum
      (fun index => (expression.action increments index).kernel)
      (count + 1) function measurable

/-- Read an expression at a measurable projection of its input environment. -/
public noncomputable def CausalPrefixMap.precomp
    (expression : CausalPrefixMap source target otherSource otherTarget)
    (function : epsilon → gamma)
    (measurable : MeasurableMap middle otherSource function) :
    CausalPrefixMap source target middle otherTarget where
  operator := fun continuation =>
    ⟨(expression.operator continuation).kernel.precomp function measurable,
      (expression.operator continuation).sfinite.precomp function measurable⟩
  monotone := by
    intro first second included
    exact precomp_le function measurable (expression.monotone first second included)
  continuous := by
    intro chain increasing increments finite prefix_eq
    change (expression.operator ⟨_, _⟩).kernel.precomp function measurable = _
    rw [expression.continuous chain increasing increments finite prefix_eq]
    exact precomp_iSupIncreasing
      (fun index => (expression.operator (chain index)).kernel)
      (fun index => expression.monotone _ _ (increasing index)) function measurable
  action := fun increments count =>
    ⟨(expression.action increments count).kernel.precomp function measurable,
      (expression.action increments count).sfinite.precomp function measurable⟩
  causal := by
    intro first second count equal
    exact congrArg (fun kernel : Kernel otherSource otherTarget =>
      kernel.precomp function measurable) (expression.causal first second count equal)
  prefix_eq := by
    intro increments count
    change (expression.operator (SFiniteKernel.prefixSum increments count)).kernel.precomp
      function measurable = _
    rw [expression.prefix_eq increments count]
    exact precomp_prefixSum
      (fun index => (expression.action increments index).kernel)
      (count + 1) function measurable

/-- Select one of two positive expressions from a sum-typed input. -/
public noncomputable def CausalPrefixMap.copair
    (first : CausalPrefixMap source target otherSource otherTarget)
    (second : CausalPrefixMap source target middle otherTarget) :
    CausalPrefixMap source target (Space.sum otherSource middle) otherTarget where
  operator := fun continuation =>
    ⟨Kernel.copair (first.operator continuation).kernel
        (second.operator continuation).kernel,
      (first.operator continuation).sfinite.copair
        (second.operator continuation).sfinite⟩
  monotone := by
    intro left right included input set measurable
    cases input with
    | inl value => exact first.monotone left right included value set measurable
    | inr value => exact second.monotone left right included value set measurable
  continuous := by
    intro chain increasing increments finite prefix_eq
    apply Kernel.sum_ext
    · intro input
      change (first.operator ⟨_, _⟩).kernel input = _
      rw [first.continuous chain increasing increments finite prefix_eq,
        iSupIncreasing_apply, iSupIncreasing_apply]
      rfl
    · intro input
      change (second.operator ⟨_, _⟩).kernel input = _
      rw [second.continuous chain increasing increments finite prefix_eq,
        iSupIncreasing_apply, iSupIncreasing_apply]
      rfl
  action := fun increments count =>
    ⟨Kernel.copair (first.action increments count).kernel
        (second.action increments count).kernel,
      (first.action increments count).sfinite.copair
        (second.action increments count).sfinite⟩
  causal := by
    intro left right count equal
    apply Kernel.sum_ext
    · intro input
      exact congrArg (fun kernel : Kernel otherSource otherTarget => kernel input)
        (first.causal left right count equal)
    · intro input
      exact congrArg (fun kernel : Kernel middle otherTarget => kernel input)
        (second.causal left right count equal)
  prefix_eq := by
    intro increments count
    change Kernel.copair
      (first.operator (SFiniteKernel.prefixSum increments count)).kernel
      (second.operator (SFiniteKernel.prefixSum increments count)).kernel = _
    rw [first.prefix_eq increments count, second.prefix_eq increments count]
    exact copair_prefixSum
      (fun index => (first.action increments index).kernel)
      (fun index => (second.action increments index).kernel) (count + 1)

/-- Exit paths appear at depth zero; each later increment takes one step
followed by an increment from the preceding depth. -/
@[expose] public noncomputable def SFiniteKernel.linearAction
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit)
    (increments : Nat → SFiniteKernel source target) :
    Nat → SFiniteKernel source target
  | 0 => ⟨exit, exitFinite⟩
  | count + 1 => ⟨step.comp (increments count).kernel,
      IsSFinite.comp stepFinite (increments count).sfinite⟩

/-- The linear body has a causal cumulative-increment presentation. -/
public noncomputable def CausalPrefixOperator.linear
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit) :
    CausalPrefixOperator (SFiniteKernel.linear step stepFinite exit exitFinite) where
  action := SFiniteKernel.linearAction step stepFinite exit exitFinite
  causal := by
    intro first second count same
    cases count with
    | zero => rfl
    | succ count =>
        change step.comp (first count).kernel = step.comp (second count).kernel
        rw [same count (Nat.lt_succ_self count)]
  prefix_eq := by
    intro increments count
    induction count with
    | zero =>
        change Kernel.add exit (step.comp (Kernel.zero source target)) =
          Kernel.add (Kernel.zero source target) exit
        rw [comp_zero, add_zero, zero_add]
    | succ count induction =>
        have prior : Kernel.add exit
            (step.comp (Kernel.prefixSum (fun index => (increments index).kernel) count)) =
            Kernel.prefixSum
              (fun index => (SFiniteKernel.linearAction step stepFinite exit exitFinite
                increments index).kernel) (count + 1) := induction
        change Kernel.add exit (step.comp
            (Kernel.add (Kernel.prefixSum (fun index => (increments index).kernel) count)
              (increments count).kernel)) =
          Kernel.add
            (Kernel.prefixSum
              (fun index => (SFiniteKernel.linearAction step stepFinite exit exitFinite
                increments index).kernel) (count + 1))
            (step.comp (increments count).kernel)
        rw [comp_add_distrib, ← add_assoc, prior]

/-- The increment at depth `n` consults only the earlier constructed
increments. The truncated family makes this a well-founded recursion. -/
@[expose] public noncomputable def CausalPrefixOperator.fixedIncrements
    {operator : SFiniteKernel source target → SFiniteKernel source target}
    (action : CausalPrefixOperator operator) (count : Nat) :
    SFiniteKernel source target :=
  action.action
    (fun index => if _earlier : index < count then action.fixedIncrements index
      else SFiniteKernel.zero source target) count
termination_by count

/-- The guarded definition solves the increment equation at every depth. -/
public theorem CausalPrefixOperator.fixedIncrements_eq_action
    {operator : SFiniteKernel source target → SFiniteKernel source target}
    (action : CausalPrefixOperator operator) (count : Nat) :
    (action.fixedIncrements count).kernel =
      (action.action action.fixedIncrements count).kernel := by
  unfold fixedIncrements
  apply action.causal
  intro index earlier
  simp [earlier]

/-- Finite zero-based unfoldings retain an s-finite witness at every depth. -/
@[expose] public noncomputable def sfiniteFixedPointApproximant
    (operator : SFiniteKernel source target → SFiniteKernel source target) :
    Nat → SFiniteKernel source target
  | 0 => ⟨Kernel.zero source target, IsSFinite.zero source target⟩
  | count + 1 => operator (sfiniteFixedPointApproximant operator count)

/-- Each witnessed unfolding includes the previous one. -/
public theorem sfiniteFixedPointApproximant_monotone
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator) (count : Nat) :
    le (sfiniteFixedPointApproximant operator count).kernel
      (sfiniteFixedPointApproximant operator (count + 1)).kernel := by
  induction count with
  | zero => exact zero_le _
  | succ count induction => exact continuous.monotone _ _ induction

/-- A causal path decomposition supplies cumulative increments for the
operator's zero-based unfoldings. -/
public theorem CausalPrefixOperator.approximant_eq_prefixSum
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (action : CausalPrefixOperator operator) (count : Nat) :
    (sfiniteFixedPointApproximant operator count).kernel =
      Kernel.prefixSum (fun index => (action.fixedIncrements index).kernel) count := by
  have prefixes : ∀ index,
      Kernel.prefixSum
        (fun step => (action.action action.fixedIncrements step).kernel) index =
      Kernel.prefixSum (fun step => (action.fixedIncrements step).kernel) index := by
    intro index
    induction index with
    | zero => rfl
    | succ index induction =>
        rw [Kernel.prefixSum, Kernel.prefixSum, induction,
          action.fixedIncrements_eq_action index]
  induction count with
  | zero => rfl
  | succ count induction =>
      change (operator (sfiniteFixedPointApproximant operator count)).kernel = _
      have same := PrefixContinuous.congr_kernel operator continuous
        (sfiniteFixedPointApproximant operator count)
        (SFiniteKernel.prefixSum action.fixedIncrements count) induction
      rw [same, action.prefix_eq action.fixedIncrements count,
        prefixes (count + 1)]

/-- The zero-based limit is s-finite when its stages have a cumulative
increment presentation. -/
@[expose] public noncomputable def sfiniteLeastFixedPoint
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      (sfiniteFixedPointApproximant operator index).kernel = prefixSum increments index) :
    SFiniteKernel source target :=
  ⟨iSupIncreasing (fun index => (sfiniteFixedPointApproximant operator index).kernel)
      (sfiniteFixedPointApproximant_monotone operator continuous),
    IsSFinite.ofPrefixSum
      (fun index => (sfiniteFixedPointApproximant operator index).kernel)
      (sfiniteFixedPointApproximant_monotone operator continuous)
      increments finite prefix_eq⟩

/-- Substitution of the source environment commutes with each zero-based
unrolling when the witnessed body operators agree under precomposition. -/
public theorem sfinite_fixed_point_approximant_precomp
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (otherOperator : SFiniteKernel otherSource target → SFiniteKernel otherSource target)
    (function : gamma → alpha)
    (measurable : MeasurableMap otherSource source function)
    (compatible : ∀ (first : SFiniteKernel source target)
      (second : SFiniteKernel otherSource target),
      second.kernel = first.kernel.precomp function measurable →
      (otherOperator second).kernel = (operator first).kernel.precomp function measurable)
    (count : Nat) :
    (sfiniteFixedPointApproximant otherOperator count).kernel =
      (sfiniteFixedPointApproximant operator count).kernel.precomp function measurable := by
  induction count with
  | zero => rfl
  | succ count induction => exact compatible _ _ induction

/-- The same compatibility law carries the entire witnessed least kernel
through a measurable change of source environment. -/
public theorem sfinite_least_fixed_point_precomp
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      (sfiniteFixedPointApproximant operator index).kernel = prefixSum increments index)
    (otherOperator : SFiniteKernel otherSource target → SFiniteKernel otherSource target)
    (otherContinuous : PrefixContinuous otherOperator)
    (otherIncrements : Nat → Kernel otherSource target)
    (otherFinite : ∀ index, IsSFinite (otherIncrements index))
    (otherPrefixEq : ∀ index,
      (sfiniteFixedPointApproximant otherOperator index).kernel =
        prefixSum otherIncrements index)
    (function : gamma → alpha)
    (measurable : MeasurableMap otherSource source function)
    (compatible : ∀ (first : SFiniteKernel source target)
      (second : SFiniteKernel otherSource target),
      second.kernel = first.kernel.precomp function measurable →
      (otherOperator second).kernel = (operator first).kernel.precomp function measurable) :
    (sfiniteLeastFixedPoint otherOperator otherContinuous otherIncrements
      otherFinite otherPrefixEq).kernel =
    (sfiniteLeastFixedPoint operator continuous increments finite prefix_eq).kernel.precomp
      function measurable := by
  apply Kernel.ext
  intro input
  apply Measure.ext
  intro region regionMeasurable
  change (iSupIncreasing
    (fun count => (sfiniteFixedPointApproximant otherOperator count).kernel)
    (sfiniteFixedPointApproximant_monotone otherOperator otherContinuous)) input region =
    (iSupIncreasing
      (fun count => (sfiniteFixedPointApproximant operator count).kernel)
      (sfiniteFixedPointApproximant_monotone operator continuous)).precomp
      function measurable input region
  rw [Kernel.precomp_apply,
    iSupIncreasing_apply_measurable _ _ input regionMeasurable,
    iSupIncreasing_apply_measurable _ _ (function input) regionMeasurable]
  apply congrArg ENNReal.iSup
  funext count
  rw [sfinite_fixed_point_approximant_precomp operator otherOperator function measurable
    compatible count]
  rfl

/-- The witnessed fixed point is one more application of its operator. -/
public theorem sfiniteLeastFixedPoint_unfold
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      (sfiniteFixedPointApproximant operator index).kernel = prefixSum increments index) :
    (operator (sfiniteLeastFixedPoint operator continuous increments finite prefix_eq)).kernel =
      (sfiniteLeastFixedPoint operator continuous increments finite prefix_eq).kernel := by
  let chain := sfiniteFixedPointApproximant operator
  let increasing := sfiniteFixedPointApproximant_monotone operator continuous
  change (operator ⟨iSupIncreasing (fun index => (chain index).kernel) increasing,
    IsSFinite.ofPrefixSum (fun index => (chain index).kernel) increasing
      increments finite prefix_eq⟩).kernel =
    iSupIncreasing (fun index => (chain index).kernel) increasing
  rw [continuous.continuous chain increasing increments finite prefix_eq]
  apply le_antisymm
  · apply iSupIncreasing_le
    intro count
    exact le_iSupIncreasing (fun index => (chain index).kernel) increasing (count + 1)
  · apply iSupIncreasing_le
    intro count
    cases count with
    | zero => exact zero_le _
    | succ count =>
        exact le_iSupIncreasing (fun index => (operator (chain index)).kernel)
          (fun index => continuous.monotone _ _ (increasing index)) count

/-- Every s-finite pre-fixed point bounds the zero-based limit. -/
public theorem sfiniteLeastFixedPoint_least
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      (sfiniteFixedPointApproximant operator index).kernel = prefixSum increments index)
    (candidate : SFiniteKernel source target)
    (prefixed : le (operator candidate).kernel candidate.kernel) :
    le (sfiniteLeastFixedPoint operator continuous increments finite prefix_eq).kernel
      candidate.kernel := by
  apply iSupIncreasing_le
  intro count
  induction count with
  | zero => exact zero_le candidate.kernel
  | succ count induction =>
      exact le_trans (continuous.monotone _ _ induction) prefixed

/-- When an operator is total and ignores its s-finite witness, the witnessed
construction agrees with the ordinary least fixed point. -/
public theorem sfiniteLeastFixedPoint_eq_leastFixedPoint
    (operator : SFiniteKernel source target → SFiniteKernel source target)
    (continuous : PrefixContinuous operator)
    (total : Kernel source target → Kernel source target)
    (totalContinuous : OmegaContinuous total)
    (agrees : ∀ (kernel : Kernel source target) (finite : IsSFinite kernel),
      (operator ⟨kernel, finite⟩).kernel = total kernel)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      (sfiniteFixedPointApproximant operator index).kernel = prefixSum increments index) :
    (sfiniteLeastFixedPoint operator continuous increments finite prefix_eq).kernel =
      leastFixedPoint total totalContinuous := by
  have approximants : ∀ count,
      (sfiniteFixedPointApproximant operator count).kernel =
        fixedPointApproximant total count := by
    intro count
    induction count with
    | zero => rfl
    | succ count induction =>
        change (operator (sfiniteFixedPointApproximant operator count)).kernel =
          total (fixedPointApproximant total count)
        rw [agrees, induction]
  apply Kernel.ext_measurable
  intro input set measurable
  change (iSupIncreasing
    (fun index => (sfiniteFixedPointApproximant operator index).kernel)
    (sfiniteFixedPointApproximant_monotone operator continuous)) input set =
      leastFixedPoint total totalContinuous input set
  rw [iSupIncreasing_apply_measurable _ _ input measurable,
    leastFixedPoint_apply_measurable total totalContinuous input measurable]
  apply congrArg ENNReal.iSup
  funext count
  exact congrArg (fun kernel : Kernel source target => kernel input set)
    (approximants count)

/-- The constructive exit-path fixed point uses increments derived from the
witnessed one-step operator. -/
@[expose] public noncomputable def SFiniteKernel.linearLeast
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit) :
    SFiniteKernel source target :=
  let operator := SFiniteKernel.linear step stepFinite exit exitFinite
  let continuous := PrefixContinuous.linear step stepFinite exit exitFinite
  let action := CausalPrefixOperator.linear step stepFinite exit exitFinite
  sfiniteLeastFixedPoint operator continuous
    (fun count => (action.fixedIncrements count).kernel)
    (fun count => (action.fixedIncrements count).sfinite)
    (action.approximant_eq_prefixSum operator continuous)

/-- The witnessed construction of a linear body is the existing loop kernel. -/
public theorem SFiniteKernel.linearLeast_eq_loop
    (step : Kernel source source) (stepFinite : IsSFinite step)
    (exit : Kernel source target) (exitFinite : IsSFinite exit) :
    (SFiniteKernel.linearLeast step stepFinite exit exitFinite).kernel =
      Kernel.loop step exit := by
  unfold SFiniteKernel.linearLeast
  rw [sfiniteLeastFixedPoint_eq_leastFixedPoint
    (SFiniteKernel.linear step stepFinite exit exitFinite)
    (PrefixContinuous.linear step stepFinite exit exitFinite)
    (fun continuation => Kernel.add exit (step.comp continuation))
    (OmegaContinuous.linear step exit)
    (by intro kernel finite; rfl)]
  exact leastFixedPoint_linear_eq_loop step exit

end Problib.Measure.Kernel
