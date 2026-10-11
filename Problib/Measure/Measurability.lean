module

public import Problib.Measure.Space.SumProduct
public import Problib.Measure.Pi
public meta import Lean.Elab.Tactic.ElabTerm

/-! The `measurability` tactic.

A measurability proof in problib is usually a term built from
`MeasurableMap.comp`, `Space.pair_measurable` and the projections, with the
same shape as the function it measures. `measurability` builds that term. It
applies one rule, which splits the function at its head, and recurses into the
parts. A composition rule closes its outer map by a closed map or a hypothesis
alone, then recurses into the smaller inner function, so the search ends.

`measurability [t₁, t₂]` adds lemmas to the context first. Each is stated at
`MeasurableMap _ _ _`, which keeps the implicit set argument of an unapplied
`MeasurableMap` lemma from being consumed. Plain `have t := lemma` would
consume it.

The tactic extends like core `decreasing_trivial`. A module adds a
`macro_rules` alternative for `measurability_atom` (a closed map) or
`measurability_split` (a decomposition rule). Each step tries every atom before
any split, so hypotheses and closed maps win over decomposition wherever the
extension is declared. `Measurability/Extended.lean` adds the
`ENNRealMeasurable` rules and `Measurability/Real.lean` the real arithmetic and
order rules.

Rules unify at reducible transparency, and a rule whose conclusion has a
different head constant from the goal, in any argument or in the measured
function, is rejected before unification. So the tactic does not unfold
definitions. A function that matches a rule only after unfolding, such as
`coordinate 0 (a :: l)` or `foldN f g 0`, needs `show` or `unfold` first. A
`Sum.elim` whose branches depend on the input closes only in the shape of
`MeasurableMap.distribute`. -/

set_option autoImplicit false

namespace Problib.Measure

public section

universe u v w x y
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ε : Type y}

/-- A binary map composed with two measurable arguments is measurable when the
map is measurable on the product. -/
theorem MeasurableMap.comp_pair {source : Space α} {left : Space β} {right : Space γ}
    {target : Space δ} {map : β → γ → δ} {first : α → β} {second : α → γ}
    (mapMeasurable : MeasurableMap (Space.product left right) target
      (fun input => map input.1 input.2))
    (firstMeasurable : MeasurableMap source left first)
    (secondMeasurable : MeasurableMap source right second) :
    MeasurableMap source target (fun value => map (first value) (second value)) :=
  MeasurableMap.comp mapMeasurable (Space.pair_measurable firstMeasurable secondMeasurable)

/-- A ternary map composed with three measurable arguments is measurable when
the map is measurable on the left-nested product. -/
theorem MeasurableMap.comp_triple {source : Space α} {first : Space β}
    {second : Space γ} {third : Space δ} {target : Space ε} {map : β → γ → δ → ε}
    {firstMap : α → β} {secondMap : α → γ} {thirdMap : α → δ}
    (mapMeasurable : MeasurableMap (Space.product (Space.product first second) third)
      target (fun input => map input.1.1 input.1.2 input.2))
    (firstMeasurable : MeasurableMap source first firstMap)
    (secondMeasurable : MeasurableMap source second secondMap)
    (thirdMeasurable : MeasurableMap source third thirdMap) :
    MeasurableMap source target
      (fun value => map (firstMap value) (secondMap value) (thirdMap value)) :=
  MeasurableMap.comp mapMeasurable (Space.pair_measurable
    (Space.pair_measurable firstMeasurable secondMeasurable) thirdMeasurable)

/-- A binary map with a fixed right argument, composed with a measurable left
argument. `MeasurableMap.comp` cannot split `map (first value) second`, because
first-order unification peels the fixed argument off first. -/
theorem MeasurableMap.comp_fixed_right {source : Space α} {middle : Space β}
    {target : Space δ} {map : β → γ → δ} {first : α → β} {second : γ}
    (mapMeasurable : MeasurableMap middle target (fun input => map input second))
    (firstMeasurable : MeasurableMap source middle first) :
    MeasurableMap source target (fun value => map (first value) second) :=
  MeasurableMap.comp mapMeasurable firstMeasurable

/-- A ternary map with a fixed middle argument, measurable on the pair of its
outer arguments, composed with two measurable arguments. The type of the last
argument may depend on the middle one, as in `replace point site value`.
`MeasurableMap.comp_triple` would need the map measurable in all three. -/
theorem MeasurableMap.comp_fixed_middle {κ : Type w} {μ : κ → Type x} {source : Space α}
    {left : Space β} {middle : κ} {right : Space (μ middle)} {target : Space ε}
    {map : β → (index : κ) → μ index → ε} {first : α → β} {second : α → μ middle}
    (mapMeasurable : MeasurableMap (Space.product left right) target
      (fun input => map input.1 middle input.2))
    (firstMeasurable : MeasurableMap source left first)
    (secondMeasurable : MeasurableMap source right second) :
    MeasurableMap source target (fun value => map (first value) middle (second value)) :=
  MeasurableMap.comp mapMeasurable (Space.pair_measurable firstMeasurable secondMeasurable)

/-- A fixed coordinate of a measurable map into a power of one space. With
`MeasurableMap.comp_fixed_right` it reads `decode seed index` as a coordinate of
`decode seed`. -/
theorem MeasurableMap.apply_coordinate {κ : Type w} {source : Space α} {target : Space β}
    {map : α → κ → β} (mapMeasurable : MeasurableMap source (Space.pi fun _ : κ => target) map)
    (index : κ) : MeasurableMap source target (fun value => map value index) :=
  MeasurableMap.comp (Space.coordinate_measurable (fun _ : κ => target) index) mapMeasurable

/-- A measurable choice between two measurable maps. The decision procedure is
an implicit argument, so any `Decidable` instance in the goal unifies. -/
theorem MeasurableMap.ite {source : Space α} {target : Space β} {region : Set α}
    {decision : ∀ value, Decidable (region value)} {first second : α → β}
    (regionMeasurable : source.Measurable region)
    (firstMeasurable : MeasurableMap source target first)
    (secondMeasurable : MeasurableMap source target second) :
    MeasurableMap source target (fun value =>
      @_root_.ite β (region value) (decision value) (first value) (second value)) := by
  intro set setMeasurable
  have equal : Set.preimage
      (fun value => @_root_.ite β (region value) (decision value) (first value) (second value))
        set =
      Set.union (Set.inter region (Set.preimage first set))
        (Set.inter (Set.complement region) (Set.preimage second set)) := by
    apply Set.ext
    intro value
    by_cases member : region value <;>
      simp [Set.preimage, Set.union, Set.inter, Set.complement, member]
  rw [equal]
  exact source.union (source.inter regionMeasurable (firstMeasurable setMeasurable))
    (source.inter (source.complement regionMeasurable) (secondMeasurable setMeasurable))

/-- Pairing each side of a measurable sum with a measurable value is
measurable. Its function is a pattern in `selector` and `captured`, so `apply`
finds both, where `MeasurableMap.comp` would split the `Sum.elim` wrongly. -/
theorem MeasurableMap.distribute {source : Space α} {left : Space β} {right : Space γ}
    {parameter : Space δ} {selector : α → Sum β γ} {captured : α → δ}
    (selectorMeasurable : MeasurableMap source (Space.sum left right) selector)
    (capturedMeasurable : MeasurableMap source parameter captured) :
    MeasurableMap source
      (Space.sum (Space.product left parameter) (Space.product right parameter))
      (fun value => Sum.elim (fun inner => Sum.inl (inner, captured value))
        (fun inner => Sum.inr (inner, captured value)) (selector value)) :=
  MeasurableMap.comp (Space.distribute_sum_measurable left right parameter)
    (Space.pair_measurable selectorMeasurable capturedMeasurable)

end

end Problib.Measure

/-- `measurability` closes a `MeasurableMap` or `ENNRealMeasurable` goal by
decomposing the function. -/
syntax (name := measurability) "measurability" (" [" term,* "]")? : tactic

/-- One step of `measurability`: a closed map, or else one split. -/
syntax (name := measurabilityCore) "measurability_core" : tactic

/-- A closed measurable map, used as the outer map of a composition. Extensions
add alternatives. -/
syntax (name := measurabilityAtom) "measurability_atom" : tactic

/-- One decomposition rule, which recurses into its parts through
`measurability_core`. Extensions add alternatives. -/
syntax (name := measurabilitySplit) "measurability_split" : tactic

/-- `apply` at reducible transparency that keeps only propositional premises as
goals. Spaces, functions and other data stay metavariables, so solving the
outer map of a composition fixes the middle space for the inner map. Reducible
unification rejects a wrong rule by syntax, without unfolding spaces such as
`Space.list` into their generated structures. No rule splits
`fun x => x`, which structure eta would otherwise turn into `(x.1, x.2)` and
back, so an identity closes only by `MeasurableMap.identity` or a hypothesis. -/
syntax (name := measurabilityApply) "measurability_apply " term : tactic

open Lean Meta in
/-- The source space and the eta-reduced function of a `MeasurableMap` goal. -/
public meta def measurabilityParts? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  if type.isAppOfArity ``Problib.Measure.MeasurableMap 5 then
    return some (type.getArg! 2, (type.getArg! 4).eta)
  return none

open Lean Meta in
/-- The head constants of a goal: the goal itself, each argument but the last
up to reducible unfolding, and the function or set it measures, looked through
one binder, `let` and beta but no definition. `none` marks a metavariable or
variable head, which any constant may still unify with. -/
public meta def measurabilityHeads (type : Expr) :
    MetaM (Option Name × Array (Option Name) × Option Name) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  let kind := type.getAppFn.constName?
  let arguments := type.getAppArgs
  if arguments.isEmpty then
    return (kind, #[], none)
  let leading ← arguments.pop.mapM fun argument =>
    return (← whnfR argument).getAppFn.constName?
  let measured := arguments.back!.eta
  let head ← if measured.isLambda then
      lambdaBoundedTelescope measured 1 fun _ body =>
        return (← whnfCore body).getAppFn.constName?
    else
      pure (← whnfCore measured).getAppFn.constName?
  return (kind, leading, head)

open Lean Elab Tactic in
/-- Fails when the named lemma cannot apply because its conclusion, one of the
conclusion's spaces, or the head of the function it measures is a different
constant from the goal's. Most rules fail this way, and the check costs no
unification. -/
public meta def measurabilityFilter (value : Syntax) : TacticM Unit := withMainContext do
  unless value.isIdent do
    return
  let name ← try realizeGlobalConstNoOverload value catch _ => return
  let (goalKind, goalArguments, goalHead) ← measurabilityHeads (← getMainTarget)
  let (lemmaKind, lemmaArguments, lemmaHead) ←
    Meta.forallTelescope (← getConstInfo name).type fun _ conclusion =>
      measurabilityHeads conclusion
  let clash : Option Name → Option Name → Bool
    | some goal, some lemma => goal != lemma
    | _, _ => false
  if clash goalKind lemmaKind || clash goalHead lemmaHead ||
      (goalArguments.size == lemmaArguments.size &&
        (goalArguments.zip lemmaArguments).any fun (goal, lemma) => clash goal lemma) then
    throwError "measurability: {name} does not match the goal's head constants"

open Lean Elab Tactic in
@[tactic measurabilityApply] public meta def evalMeasurabilityApply : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_apply $value) => do
    measurabilityFilter value
    evalApplyLikeTactic (fun goal lemma => Meta.withReducible do
      let identity := match ← measurabilityParts? (← goal.getType) with
        | some (_, .lam _ _ (.bvar 0) _) => true
        | _ => false
      let premises ← (← goal.apply lemma).filterM fun premise => do
        Meta.isProp (← premise.getType)
      if identity then
        for premise in premises do
          if (← measurabilityParts? (← premise.getType)).isSome then
            throwError "measurability: an identity map is closed, not split"
      pure premises) value
  | _ => throwUnsupportedSyntax

/-- `assumption` at reducible transparency. -/
syntax (name := measurabilityAssumption) "measurability_assumption" : tactic

open Lean Elab Tactic in
@[tactic measurabilityAssumption] public meta def evalMeasurabilityAssumption : Tactic :=
  fun _ => do Meta.withReducible (evalTactic (← `(tactic| assumption)))

/-- Fails unless the goal's function is a lambda whose body is an application
of the named constant, or the eta-reduced form of one, such as `Prod.mk value`
for `fun x => (value, x)`. `Space.pair_measurable` has a variable head, so the
filter passes it, and it would match any map into a product by structure eta. -/
syntax (name := measurabilityHead) "measurability_head " ident : tactic

open Lean Elab Tactic in
@[tactic measurabilityHead] public meta def evalMeasurabilityHead : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_head $head) => withMainContext do
    let name ← realizeGlobalConstNoOverloadWithInfo head
    let some (_, function) ← measurabilityParts? (← getMainTarget)
      | throwError "measurability_head: the goal is not `MeasurableMap`"
    let function ← instantiateMVars function
    let applied ← if function.isLambda then
        Meta.lambdaBoundedTelescope function 1 fun _ body =>
          return (← Meta.whnfCore body).isAppOf name
      else
        pure ((← Meta.whnfCore function).isAppOf name)
    unless applied do
      throwError "measurability_head: the function is not an application of {name}"
  | _ => throwUnsupportedSyntax

/-- `MeasurableMap.from_discrete` on a goal whose source is already
`Space.discrete`. Unguarded, it would fix an unknown source space to a discrete
one and break the goal that later determines it. -/
syntax (name := measurabilityDiscrete) "measurability_discrete" : tactic

open Lean Elab Tactic in
@[tactic measurabilityDiscrete] public meta def evalMeasurabilityDiscrete : Tactic :=
  fun _ => withMainContext do
  let some (source, _) ← measurabilityParts? (← getMainTarget)
    | throwError "measurability_discrete: the goal is not `MeasurableMap`"
  unless source.isAppOf ``Problib.Measure.Space.discrete do
    throwError "measurability_discrete: the source space is not `Space.discrete`"
  evalTactic (← `(tactic| exact Problib.Measure.MeasurableMap.from_discrete _ _))

/-- Fails unless the goal is an application of the named constant. A group of
rules for one kind of goal sits behind this guard, so other goals skip the
group in one check. -/
syntax (name := measurabilityGoal) "measurability_goal " ident : tactic

open Lean Elab Tactic in
@[tactic measurabilityGoal] public meta def evalMeasurabilityGoal : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_goal $head) => withMainContext do
    let name ← realizeGlobalConstNoOverloadWithInfo head
    unless (← instantiateMVars (← getMainTarget)).cleanupAnnotations.isAppOf name do
      throwError "measurability_goal: the goal is not an application of {name}"
  | _ => throwUnsupportedSyntax

/-- Fails unless the goal is `MeasurableMap` into an application of the named
constant, such as `Space.discrete` or a Borel space. -/
syntax (name := measurabilityTarget) "measurability_target " ident : tactic

open Lean Elab Tactic in
@[tactic measurabilityTarget] public meta def evalMeasurabilityTarget : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_target $head) => withMainContext do
    let name ← realizeGlobalConstNoOverloadWithInfo head
    let goal := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
    unless goal.isAppOfArity ``Problib.Measure.MeasurableMap 5 &&
        (goal.getArg! 3).isAppOf name do
      throwError "measurability_target: the target is not an application of {name}"
  | _ => throwUnsupportedSyntax

/-! ### Failure reports

A call that succeeds runs the search once and records nothing. When the search
fails, `measurability` runs it again with the option `measurability.explain`
set. On that run each goal that no rule closes is recorded as `unmatched`. Each
outer map of a composition that no closed map covers is recorded as `missing`.
Both carry the depth of the split that reached them. Backtracking restores all
elaboration state except the trace state, so each record is a tagged trace
element. The report takes the records out again and names the smallest failing
part. -/

open Lean Meta in
/-- The function a `MeasurableMap` or `ENNRealMeasurable` goal measures. -/
public meta def measurabilityFunction? (type : Expr) : MetaM (Option Expr) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  if type.isAppOfArity ``Problib.Measure.MeasurableMap 5 ||
      type.isAppOfArity `Problib.Measure.ENNRealMeasurable 3 then
    return type.getAppArgs.back?
  return none

open Lean Meta in
/-- The head constant of a measured function, read through one binder the way
the head filter reads it. `none` marks a variable or metavariable head. -/
public meta def measurabilityFunctionHead (function : Expr) : MetaM (Option Name) := do
  let function := (← instantiateMVars function).eta
  if function.isLambda then
    lambdaBoundedTelescope function 1 fun _ body =>
      return (← whnfCore body).getAppFn.constName?
  else
    return (← whnfCore function).getAppFn.constName?

open Lean Meta in
/-- A hypothesis that measures a function with the same head in another shape,
such as a lemma about `decode` beside a goal about `decode seed index`. -/
public meta def measurabilitySameHead? (head : Name) (function : Expr) :
    MetaM (Option Expr) := do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let some measured ← measurabilityFunction? declaration.type | continue
    if (← measurabilityFunctionHead measured) == some head &&
        !(← withReducible (isDefEq measured function)) then
      return some (← instantiateMVars declaration.type)
  return none

open Lean Meta Elab Tactic in
/-- On an explaining run, records that the function of `goal` failed at `depth`.
`kind` is `missing` or `unmatched`, and `rule` names the composition that
needed the outer map. The record also keeps the function's expression depth,
so the report can prefer the smallest failing part. -/
public meta def measurabilityRecord (kind rule : Name) (depth : Nat) (goal : MVarId) :
    TacticM Unit := do
  unless ← getBoolOption `measurability.explain do return
  goal.withContext do
    let some function ← measurabilityFunction? (← goal.getType) | return
    let function ← instantiateMVars function
    if function.getAppFn.isMVar then return
    let head := (← measurabilityFunctionHead function).getD .anonymous
    let hint ← match ← measurabilitySameHead? head function with
      | some type => pure (.tagged `hint (← addMessageContext (indentExpr type)))
      | none => pure (.tagged `noHint .nil)
    let body ← addMessageContext (indentExpr function)
    let rule := rule.eraseMacroScopes.replacePrefix `Problib.Measure .anonymous
    let element : TraceElem := {
      ref := ← getRef
      msg := .tagged (.num (.num (`measurability ++ kind) depth) function.approxDepth.toNat)
        (.tagged head (.tagged rule (.compose body hint))) }
    modifyTraceState fun state => { state with traces := state.traces.push element }

/-- One failure an explaining run recorded. -/
public meta structure MeasurabilityFailure where
  missing : Bool
  depth : Nat
  size : Nat
  head : Lean.Name
  rule : Lean.Name
  function : Lean.MessageData
  hint : Option Lean.MessageData

/-- Reads a record back from its trace element. -/
public meta def MeasurabilityFailure.ofTrace? : Lean.MessageData → Option MeasurabilityFailure
  | .tagged (.num (.num (.str (.str .anonymous "measurability") kind) depth) size)
      (.tagged head (.tagged rule (.compose function (.tagged tag hint)))) =>
    some { missing := kind == "missing", depth, size, head, rule, function,
           hint := if tag == `hint then some hint else none }
  | _ => none

/-- Whether `left` explains a failure better than `right`: the smaller failing
part is the more specific one, a missing premise says more than an unmatched
goal, and a deeper record lies further along the search. -/
public meta def MeasurabilityFailure.before (left right : MeasurabilityFailure) : Bool :=
  if left.size != right.size then left.size < right.size
  else if left.missing != right.missing then left.missing
  else left.depth > right.depth

open Lean Meta in
/-- What to try next for a failure: restate a hint of another shape, pass a
registered lemma for its head, or unfold a definition the tactic does not
unfold. -/
public meta def measurabilitySuggestion (failure : MeasurabilityFailure) :
    MetaM MessageData := do
  let subject := if failure.missing then "that outer map"
    else if failure.depth == 0 then "this function" else "that part"
  if let some hint := failure.hint then
    return m!"state a hint for exactly {subject}. The hypothesis{hint}\n\
      measures `{MessageData.ofConstName failure.head}` in another shape, and the tactic \
      matches shapes first-order."
  if failure.head.isAnonymous then
    return m!"add a hypothesis that measures exactly {subject}, or prove this step by hand."
  let env ← getEnv
  let candidates := #[failure.head.appendAfter "_measurable",
    `Problib.Measure ++ Name.mkSimple (failure.head.getString! ++ "_measurable")]
  if let some candidate := candidates.find? env.contains then
    return m!"pass `{MessageData.ofConstName candidate}` as a hint, \
      `measurability [{MessageData.ofConstName candidate}]`."
  if let some (.defnInfo info) := env.find? failure.head then
    if !(env.isProjectionFn failure.head) && !(← isReducible info.name) then
      return m!"`unfold {MessageData.ofConstName failure.head}` first, since the tactic does \
        not unfold definitions, or pass a hint that measures exactly {subject}."
  return m!"add a hypothesis that measures exactly {subject}, or prove this step by hand."

open Lean Meta in
/-- The report for a failed call on `goal`: what failed, where the search
stopped, and what to try next. -/
public meta def measurabilityReportMessage (goal : MVarId)
    (failures : Array MeasurabilityFailure) : MetaM MessageData := goal.withContext do
  let some function ← measurabilityFunction? (← goal.getType)
    | return m!"measurability: the goal is not `MeasurableMap` or `ENNRealMeasurable`"
  let function ← instantiateMVars function
  let head := match ← measurabilityFunctionHead function with
    | some name => m!"`{MessageData.ofConstName name}`"
    | none => m!"a variable"
  let header ← addMessageContext
    m!"measurability could not prove this function measurable:{indentExpr function}\n\
      Its head is {head}."
  let some best := (failures.qsort MeasurabilityFailure.before)[0]? | return header
  let place := match best.depth with
    | 0 => m!""
    | 1 => m!" after 1 split"
    | depth => m!" after {depth} splits"
  let cause :=
    if best.missing then
      m!"The rule `{best.rule}` matched{place}, but no hint or registered map \
        measures its outer map:{best.function}"
    else if best.depth == 0 then
      m!"No rule matched it."
    else
      m!"No rule matched this part{place}:{best.function}"
  return m!"{header}\n{cause}\nNext: {← measurabilitySuggestion best}"

/-- Runs one `measurability` search. On failure it runs the search again with
`measurability.explain` set, takes the records out of the trace state, and
throws the report. -/
syntax (name := measurabilityReport) "measurability_report " tactic : tactic

open Lean Elab Tactic in
@[tactic measurabilityReport] public meta def evalMeasurabilityReport : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_report $search) => do
    let goal ← getMainGoal
    let saved ← saveState
    try evalTactic search
    catch error =>
      saved.restore
      let start := (← getTraceState).traces.size
      let explained ← tryCatch
        (do
          withOptions (·.setBool `measurability.explain true) (evalTactic search)
          pure true)
        (fun _ => pure false)
      let traces := (← getTraceState).traces
      let mut failures := #[]
      for index in [start:traces.size] do
        if let some failure := MeasurabilityFailure.ofTrace? traces[index]!.msg then
          failures := failures.push failure
      modifyTraceState fun state => { state with traces := truncate state.traces start }
      if explained then return
      saved.restore
      if failures.isEmpty then throw error
      throwError (← measurabilityReportMessage goal failures)
  | _ => throwUnsupportedSyntax
where
  truncate (traces : PersistentArray TraceElem) (size : Nat) :
      PersistentArray TraceElem := Id.run do
    let mut traces := traces
    while size < traces.size do
      traces := traces.pop
    return traces

open Lean Elab Tactic in
@[tactic measurabilityCore] public meta def evalMeasurabilityCore : Tactic := fun _ => do
  let depth ← getNatOption `measurability.depth
  let goal ← getMainGoal
  let saved ← saveState
  try
    withOptions (·.set `measurability.depth (depth + 1)) do
      tryCatch (withoutRecover (evalTactic (← `(tactic| measurability_atom)))) fun _ => do
        saved.restore
        evalTactic (← `(tactic| measurability_split))
  catch error =>
    saved.restore
    measurabilityRecord `unmatched .anonymous depth goal
    throw error

/-- Closes the outer map of a composition, the main goal, with
`measurability_atom` alone. On an explaining run a failure records the outer
map as missing, unless an inner map is the identity: then the outer map is the
goal itself and says nothing new. -/
syntax (name := measurabilityOuter) "measurability_outer " ident : tactic

open Lean Meta Elab Tactic in
@[tactic measurabilityOuter] public meta def evalMeasurabilityOuter : Tactic := fun stx =>
  match stx with
  | `(tactic| measurability_outer $rule) => do
    let goals ← getGoals
    let saved ← saveState
    try evalTactic (← `(tactic| focus (measurability_atom; done)))
    catch error =>
      saved.restore
      if let outer :: inner := goals then
        unless ← inner.anyM (fun goal => identity goal) do
          measurabilityRecord `missing rule.getId ((← getNatOption `measurability.depth) - 1)
            outer
      throw error
  | _ => throwUnsupportedSyntax
where
  identity (goal : MVarId) : MetaM Bool := goal.withContext do
    match ← measurabilityFunction? (← goal.getType) with
    | some function => return ((← instantiateMVars function).eta matches .lam _ _ (.bvar 0) _)
    | none => return false

/-! ### Rules

`macro_rules` alternatives are tried newest first, so the atoms below run from
the last declared to the first. The splits for one kind of goal sit in one
`first` block behind a guard on that kind, tried top to bottom, so a goal pays
one check for each group that cannot apply. A composition rule closes its outer
map with `measurability_atom` alone, so the search only recurses into strictly
smaller inner functions. It tries the outer map first. If that fails and the
target is discrete, it solves the inner map first, which fixes the middle
space, so the guarded `MeasurableMap.from_discrete` can close an outer map such
as `fun n => n - 1` out of `Space.discrete Nat`. -/

/-! Closed maps. `Sum.elim` and `Sum.map` of closed maps are closed, and their
parts are strictly smaller, so the outer map of a composition may take them. A
fixed coordinate of a closed map into a power is closed, and it is declared
first, so it is tried after every other atom. -/

macro_rules
  | `(tactic| measurability_atom) => `(tactic|
      (measurability_apply Problib.Measure.MeasurableMap.apply_coordinate <;>
        measurability_atom))
macro_rules
  | `(tactic| measurability_atom) => `(tactic|
      (measurability_apply Problib.Measure.MeasurableMap.sum_map <;> measurability_core))
macro_rules
  | `(tactic| measurability_atom) => `(tactic|
      (measurability_apply Problib.Measure.MeasurableMap.sum_elim <;> measurability_core))
macro_rules
  | `(tactic| measurability_atom) => `(tactic| measurability_discrete)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Space.distribute_sum_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.MeasurableMap.inr)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.MeasurableMap.inl)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Space.coordinate_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Space.second_measurable)
macro_rules
  | `(tactic| measurability_atom) =>
    `(tactic| measurability_apply Problib.Measure.Space.first_measurable)
macro_rules
  | `(tactic| measurability_atom) => `(tactic| measurability_assumption)

/-! Decomposition of `MeasurableMap` goals, tried in order. A composition tries
its outer map first. The inner-first variants apply only into a discrete
target, where the outer map can be `MeasurableMap.from_discrete`. -/

macro_rules
  | `(tactic| measurability_split) => `(tactic|
      (measurability_goal Problib.Measure.MeasurableMap
       first
       | (measurability_apply Problib.Measure.MeasurableMap.distribute <;> measurability_core)
       | measurability_apply Problib.Measure.MeasurableMap.identity
       | measurability_apply Problib.Measure.MeasurableMap.constant
       | (measurability_head Prod.mk
          measurability_apply Problib.Measure.Space.pair_measurable <;> measurability_core)
       | (measurability_target Problib.Measure.Space.pi
          measurability_apply Problib.Measure.Space.pi_measurable
          intro
          measurability_core)
       | (measurability_apply Problib.Measure.MeasurableMap.ite <;> measurability_core)
       | (measurability_apply Problib.Measure.MeasurableMap.comp
          measurability_outer Problib.Measure.MeasurableMap.comp
          measurability_core)
       | (measurability_target Problib.Measure.Space.discrete
          measurability_apply Problib.Measure.MeasurableMap.comp
          rotate_left
          focus (measurability_core; done)
          measurability_discrete)
       | (measurability_apply Problib.Measure.MeasurableMap.comp_fixed_right
          measurability_outer Problib.Measure.MeasurableMap.comp_fixed_right
          measurability_core)
       | (measurability_target Problib.Measure.Space.discrete
          measurability_apply Problib.Measure.MeasurableMap.comp_fixed_right
          rotate_left
          focus (measurability_core; done)
          measurability_discrete)
       | (measurability_apply Problib.Measure.MeasurableMap.comp_pair
          measurability_outer Problib.Measure.MeasurableMap.comp_pair
          all_goals measurability_core)
       | (measurability_apply Problib.Measure.MeasurableMap.comp_triple
          measurability_outer Problib.Measure.MeasurableMap.comp_triple
          all_goals measurability_core)
       | (measurability_apply Problib.Measure.MeasurableMap.comp_fixed_middle
          measurability_outer Problib.Measure.MeasurableMap.comp_fixed_middle
          all_goals measurability_core)))

/-! The hints become hypotheses, and the search runs under its failure report. -/

macro_rules
  | `(tactic| measurability $[[$terms,*]]?) => do
    let mut tactic ← `(tactic| measurability_core)
    for term in ((terms.map (·.getElems)).getD #[]).reverse do
      tactic ← `(tactic|
        ((first
          | have : Problib.Measure.MeasurableMap _ _ _ := $term
          | have := $term); $tactic))
    `(tactic| focus (measurability_report $tactic:tactic))
