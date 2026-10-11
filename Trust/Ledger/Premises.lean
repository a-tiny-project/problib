import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FindExpr
import Lean.Util.ReplaceExpr
import Trust.Ledger.Registry

/-! Premise derivation and the two checks of the premise ledger.

A claim's premises are the non-dependent binders of its `∀` telescope. The
claim without premise `p` is `drop% C p`. A necessity witness must have type
`¬ drop% C p`, so it shows the conclusion failing once `p` is gone. An
independence witness, which shows only that `p` can fail while the others
hold, has another type and is refused. An inhabitant must apply the claim,
closed, to every binder but a negated conclusion, which shows that the
premises hold together at one instance. Witnesses and inhabitants must be
theorems or safe definitions, because an unsafe or partial definition may
refer to itself.

Like `#print axioms`, both checks trust that the kernel checked every
declaration a witness or inhabitant reaches. A theorem added under
`debug.skipKernelTC`, or by an `addDecl` that skips the kernel, may cite an
unsafe or partial constant or carry a value of another type, and both checks
accept it and anything that rests on it. Replaying the declaring module
through the kernel, as `leanchecker` does, refuses it. -/

namespace Trust.Ledger

open Lean Meta

/-- How a claim meets the ledger. -/
inductive ClaimKind where
  /-- The type is not a proposition. No obligations. -/
  | definition
  /-- A proposition with no binders. No obligations. -/
  | closed
  /-- Binders, none of them a premise. Needs an inhabitant. -/
  | unconditional
  /-- At least one premise. Needs an inhabitant and a witness per premise. -/
  | conditional
deriving Inhabited, BEq, Repr

def ClaimKind.label : ClaimKind → String
  | .definition => "definition"
  | .closed => "closed"
  | .unconditional => "unconditional"
  | .conditional => "conditional"

/-- The binder a premise comes from. -/
inductive PremiseSort where
  /-- A proposition: an antecedent, or a field of a split record. -/
  | prop
  /-- A proposition class instance, such as `[NeZero N]`. -/
  | inst
  /-- Data that the conclusion never mentions, such as a certificate. -/
  | data
deriving Inhabited, BEq, Repr

def PremiseSort.label : PremiseSort → String
  | .prop => "prop"
  | .inst => "instance"
  | .data => "data"

/-- One premise: a non-dependent binder, or one field of a split record. -/
structure Premise where
  /-- The binder's name, `binder.field` for a field, or `arg<k>`. -/
  id : Name
  /-- The telescope position of the binder. -/
  binder : Nat
  /-- The field indices from the binder down to this premise. -/
  path : List Nat
  sort : PremiseSort
deriving Inhabited, BEq, Repr

/-- The ledger's reading of a claim's statement. -/
structure Shape where
  kind : ClaimKind
  /-- The binders an inhabitant applies the claim to: all of them, except a
  negated conclusion. -/
  arity : Nat := 0
  premises : Array Premise := #[]
  /-- Dependent data binders. Their arguments name an inhabitant's instance. -/
  parameters : Array (Name × Nat) := #[]
  /-- Dependent proposition binders. Dropping one is ill-formed, so none has
  a necessity obligation. -/
  dependent : Array Name := #[]
  /-- Dependent binders of registered records. Each stays an open obligation
  until its record is unbundled. -/
  bundled : Array Name := #[]
  /-- The last binder of a claim that concludes `False`. -/
  negated : Option Name := none
  /-- A closed claim whose conclusion unfolds to a `∀` at default
  transparency, so premises may hide behind a definition. -/
  wrapped : Bool := false
deriving Inhabited, Repr

/-- Records split at most this many levels below their binder. -/
def splitDepth : Nat := 3

private def argName (position : Nat) : Name :=
  Name.mkSimple s!"arg{position}"

private def isArgName : Name → Bool
  | .str .anonymous text =>
      match text.toList with
      | 'a' :: 'r' :: 'g' :: digits => !digits.isEmpty && digits.all Char.isDigit
      | _ => false
  | _ => false

/-- A binder's id is its user name when that name is accessible and no other
binder carries it, and `arg<k>` otherwise. Ids are therefore distinct. -/
private def binderIds (declarations : Array LocalDecl) : Array Name :=
  let names := declarations.map fun declaration =>
    let name := declaration.userName
    if name.isAnonymous || name.hasMacroScopes ||
        name.isInaccessibleUserName || isArgName name then
      none
    else
      some name
  names.mapIdx fun position name? =>
    match name? with
    | some name =>
        if (names.filter (· == some name)).size == 1 then name
        else argName position
    | none => argName position

/-- The fields of a record that splits into premises: a structure that is no
class, has at least two fields, none depending on another, and is either a
proposition or a registered premise record. -/
private def splitFields? (type : Expr) :
    MetaM (Option (Array (Name × Expr))) := do
  let type := type.cleanupAnnotations
  let .const structName levels := type.getAppFn | return none
  let environment ← getEnv
  unless isStructure environment structName do return none
  if isClass environment structName then return none
  let fieldNames := getStructureFields environment structName
  unless fieldNames.size ≥ 2 do return none
  unless isPremiseRecord environment structName || (← isProp type) do
    return none
  let constructor := getStructureCtor environment structName
  let arguments := type.getAppArgs
  unless arguments.size == constructor.numParams do return none
  let constructorType ← instantiateForall
    (constructor.type.instantiateLevelParams constructor.levelParams levels)
    arguments
  forallTelescope constructorType fun fields _ => do
    unless fields.size == fieldNames.size do return none
    let mut result := #[]
    for (field, fieldName) in fields.zip fieldNames do
      let fieldType ← inferType field
      if fields.any fun other => fieldType.containsFVar other.fvarId! then
        return none
      result := result.push (fieldName, fieldType)
    return some result

/-- One leaf of a binder: the binder itself, or a field of a split record. -/
private structure Leaf where
  id : Name
  path : List Nat
  type : Expr

/-- The leaves of a binder of type `type`, splitting records at most `fuel`
levels deep. Fields keep declaration order. -/
private def leaves : Nat → Name → List Nat → Expr → MetaM (Array Leaf)
  | 0, id, path, type => return #[{ id, path, type }]
  | fuel + 1, id, path, type => do
      let some fields ← splitFields? type | return #[{ id, path, type }]
      let mut result := #[]
      let mut index := 0
      for (fieldName, fieldType) in fields do
        result := result ++
          (← leaves fuel (id ++ fieldName) (path ++ [index]) fieldType)
        index := index + 1
      return result

/-- A closed claim whose conclusion unfolds to a `∀`. A negation stays a
conclusion, as the telescope reads it. -/
private def isWrapped (conclusion : Expr) : MetaM Bool := do
  if (← whnfR conclusion).isAppOf ``Not then return false
  return (← whnfD conclusion).isForall

/-- The shape of a claim inside its telescope, with every binder's id. -/
private def shapeIn (xs : Array Expr) (conclusion : Expr) :
    MetaM (Shape × Array Name) := do
  let declarations ← xs.mapM fun x => x.fvarId!.getDecl
  let ids := binderIds declarations
  let negated := !xs.isEmpty && conclusion.consumeMData.isConstOf ``False
  let arity := if negated then xs.size - 1 else xs.size
  let mut shape : Shape := {
    kind := .closed
    arity
    negated := if negated then ids.back? else none
  }
  for position in [0:arity] do
    let x := xs[position]!
    let declaration := declarations[position]!
    let id := ids[position]!
    let type := declaration.type
    let prop ← isProp type
    let instanceBinder := declaration.binderInfo.isInstImplicit
    if instanceBinder && !prop then continue
    let laterTypes ← (xs.extract (position + 1) xs.size).mapM inferType
    let isDependent := conclusion.containsFVar x.fvarId! ||
      laterTypes.any fun later => later.containsFVar x.fvarId!
    if isDependent then
      if prop then
        shape := { shape with dependent := shape.dependent.push id }
      else
        shape := { shape with parameters := shape.parameters.push (id, position) }
        let head := type.cleanupAnnotations.getAppFn
        if head.isConst && isPremiseRecord (← getEnv) head.constName! then
          shape := { shape with bundled := shape.bundled.push id }
      continue
    for leaf in ← leaves splitDepth id [] type do
      let sort ←
        if instanceBinder then pure PremiseSort.inst
        else if ← isProp leaf.type then pure PremiseSort.prop
        else pure PremiseSort.data
      shape := { shape with
        premises := shape.premises.push {
          id := leaf.id, binder := position, path := leaf.path, sort } }
  let kind :=
    if !shape.premises.isEmpty then ClaimKind.conditional
    else if arity == 0 then ClaimKind.closed
    else ClaimKind.unconditional
  let wrapped ← if arity == 0 then isWrapped conclusion else pure false
  return ({ shape with kind, wrapped }, ids)

/-- Runs `k` inside the claim's `∀` telescope, taken at reducible
transparency: an `abbrev` unfolds, and an ordinary `def`, `Not` included,
does not. `k` itself runs at default transparency. -/
def claimTelescope {α : Type} (type : Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α :=
  withReducible <| forallTelescopeReducing type fun xs conclusion =>
    withTransparency .default (k xs conclusion)

/-- The ledger's reading of a claim with type `type`. -/
def shapeOf (type : Expr) : MetaM Shape := do
  unless ← isProp type do return { kind := .definition }
  claimTelescope type fun xs conclusion =>
    return (← shapeIn xs conclusion).1

private def listNames (names : Array Name) : String :=
  s!"[{formatNames names}]"

private def notAPremise (target : Name) (shape : Shape) : MessageData :=
  if shape.bundled.contains target then
    m!"{target} is bundled. Its record must be unbundled before a witness \
      can break the claim without it"
  else if shape.dependent.contains target then
    m!"{target} is a dependent binder, so dropping it is ill-formed"
  else if shape.negated == some target then
    m!"{target} is the negated conclusion"
  else
    let others :=
      (if shape.dependent.isEmpty then ""
        else s!", dependent {listNames shape.dependent}") ++
      (if shape.bundled.isEmpty then ""
        else s!", bundled {listNames shape.bundled}")
    m!"{target} is not a premise. Premises \
      {listNames (shape.premises.map (·.id))}{others}"

/-- The type of claim `C` without premise `target`: `drop% C target`. A split
record keeps its other fields as binders, in declaration order. Every other
binder keeps its binder info. -/
def dropType (type : Expr) (target : Name) :
    MetaM (Except MessageData Expr) := do
  unless ← isProp type do
    return .error m!"a definition has no premises"
  claimTelescope type fun xs conclusion => do
    let (shape, ids) ← shapeIn xs conclusion
    let some premise := shape.premises.find? (·.id == target)
      | return .error (notAPremise target shape)
    let position := premise.binder
    let binderType ← inferType xs[position]!
    let kept := (← leaves splitDepth ids[position]! [] binderType).filter
      (·.id != target)
    let fields := kept.map fun leaf =>
      match leaf.id with
      | .str _ text => (Name.mkSimple text, leaf.type)
      | _ => (leaf.id, leaf.type)
    let dropped ← withLocalDeclsDND fields fun fieldVariables =>
      mkForallFVars
        (xs.extract 0 position ++ fieldVariables ++
          xs.extract (position + 1) xs.size)
        conclusion
    return .ok dropped

/-- The field path of a projection chain rooted at `x`, outermost field
last. -/
private def projectionPath (environment : Environment) (x : FVarId) :
    Expr → Option (List Nat)
  | .fvar y => if y == x then some [] else none
  | .mdata _ inner => projectionPath environment x inner
  | .proj _ index inner =>
      (projectionPath environment x inner).map (· ++ [index])
  | .app function inner =>
      match function.getAppFn with
      | .const name _ =>
          match environment.getProjectionFnInfo? name with
          | some info =>
              if function.getAppNumArgs == info.numParams then
                (projectionPath environment x inner).map (· ++ [info.i])
              else none
          | none => none
      | _ => none
  | _ => none

/-- Whether `proof` reads the premise at `path` below binder `x`. A projection
chain from `x` reads the fields along it, and any other occurrence of `x`
reads the whole binder. Chains to fields off the path are pruned, and the
premise is read when `x` still occurs. -/
private def readsPremise (environment : Environment) (x : FVarId)
    (path : List Nat) (proof : Expr) : Bool :=
  let pruned := proof.replace fun term =>
    if !term.hasFVar then some term
    else
      match projectionPath environment x term with
      | some read =>
          if read.isPrefixOf path || path.isPrefixOf read then none
          else some (.lit (.natVal 0))
      | none => none
  (pruned.find? fun term =>
    match term with
    | .fvar y => y == x
    | _ => false).isSome

/-- The premises the claim's proof never reads, or `none` when the proof is
not in the environment. An unread premise is unused: the same proof proves the
claim without it, so no necessity witness can exist. A record passed along
whole, or read through `casesOn` or an auxiliary lemma, counts as read. -/
def unusedPremises (info : ConstantInfo) : MetaM (Option (Array Name)) := do
  let some value := info.value? (allowOpaque := true) | return none
  unless ← isProp info.type do return some #[]
  claimTelescope info.type fun xs conclusion => do
    let (shape, _) ← shapeIn xs conclusion
    let proof := value.beta xs
    let environment ← getEnv
    return some <| shape.premises.filterMap fun premise =>
      if readsPremise environment xs[premise.binder]!.fvarId! premise.path
          proof then
        none
      else
        some premise.id

private def withoutObligation? (claim : Name) (shape : Shape) :
    Option MessageData :=
  match shape.kind with
  | .definition => some m!"{claim} is a definition, which has no obligations"
  | .closed => some m!"{claim} is closed, which has no obligations"
  | _ => none

private def policyProblem? (policy : Policy) (declaration : Name) :
    MetaM (Option MessageData) := do
  let rejected := sortedNames <| (← collectAxioms declaration).filter
    fun axiomName => !policy.permits axiomName
  if rejected.isEmpty then return none
  return some m!"{declaration} depends on axioms outside the claim's policy \
    {listNames rejected}"

/-- The value of `declaration` when it may serve as a witness or an
inhabitant: a theorem or a safe definition. An unsafe or partial definition
may refer to itself, so its value can have any type, a false one included.
When the kernel checked this declaration and everything its value reaches, no
unsafe or partial constant is reachable, because the kernel refuses a safe
value that cites one. A declaration added without that check, as under
`debug.skipKernelTC`, may cite one, and this test cannot tell. -/
private def safeValue (declaration : Name) :
    ConstantInfo → Except MessageData Expr
  | .thmInfo info => .ok info.value
  | .defnInfo info =>
      match info.safety with
      | .safe => .ok info.value
      | .unsafe => .error m!"{declaration} is an unsafe definition, which may \
          refer to itself"
      | .partial => .error m!"{declaration} is a partial definition, which may \
          refer to itself"
  | _ => .error m!"{declaration} is not a theorem or definition"

/-- Whether `a` and `b` are definitionally equal under one assignment of their
level metavariables. `isDefEq` alone may return `true` with level constraints
postponed that no assignment satisfies, such as `?v =?= max ?u (?v + 1)`.
Every postponed constraint must be solved here, and a failure restores the
metavariable context. -/
private def isDefEqAtSomeLevels (a b : Expr) : MetaM Bool :=
  checkpointDefEq (mayPostpone := false) (isDefEq a b)

/-- Accepts `witness` for premise `premise` of `claim` when it is a theorem or
a safe definition, its type is definitionally `¬ drop% claim premise` at
default transparency, and its axioms fit the policy of the group that
registers the claim. Universe parameters on both sides become metavariables,
so a witness may fix levels or stay polymorphic, but one assignment of them
must solve every level constraint. -/
def checkNecessity (claim premise witness : Name) :
    MetaM (Except MessageData Unit) := do
  let environment ← getEnv
  let some policy := claimPolicy? environment claim
    | return .error m!"{claim} is not a registered claim"
  let info ← getConstInfo claim
  let shape ← shapeOf info.type
  if let some reason := withoutObligation? claim shape then
    return .error reason
  let witnessInfo ← getConstInfo witness
  if let .error reason := safeValue witness witnessInfo then
    return .error reason
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let dropped ←
    match ← dropType (info.instantiateTypeLevelParams levels) premise with
    | .ok dropped => pure dropped
    | .error reason => return .error reason
  let witnessLevels ← witnessInfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let witnessType := witnessInfo.instantiateTypeLevelParams witnessLevels
  unless ← isDefEqAtSomeLevels witnessType (mkNot dropped) do
    let shown ←
      match ← dropType info.type premise with
      | .ok shown => pure shown
      | .error reason => return .error reason
    return .error m!"{witness} has type{indentExpr witnessInfo.type}\n\
      which is not{indentExpr (mkNot shown)}"
  if let some problem ← policyProblem? policy witness then
    return .error problem
  return .ok ()

/-- Accepts `inhabitant` for `claim` when it is a theorem or a safe definition
whose value applies the claim to at least its arity of arguments, with no
loose bound variable, free variable or metavariable, and whose axioms fit the
claim's policy. Returns the instance: the arguments at the claim's parameter
positions. -/
def checkInhabitant (claim inhabitant : Name) :
    MetaM (Except MessageData (Array (Name × Expr))) := do
  let environment ← getEnv
  let some policy := claimPolicy? environment claim
    | return .error m!"{claim} is not a registered claim"
  let info ← getConstInfo claim
  let shape ← shapeOf info.type
  if let some reason := withoutObligation? claim shape then
    return .error reason
  let value ←
    match safeValue inhabitant (← getConstInfo inhabitant) with
    | .ok value => pure value
    | .error reason => return .error reason
  let application? := value.find? fun term =>
    term.getAppFn.isConstOf claim && term.getAppNumArgs ≥ shape.arity &&
      !term.hasLooseBVars && !term.hasFVar && !term.hasMVar
  let some application := application?
    | return .error m!"{inhabitant} has no closed application of {claim} to \
        {shape.arity} arguments"
  if let some problem ← policyProblem? policy inhabitant then
    return .error problem
  let arguments := application.getAppArgs
  return .ok <| shape.parameters.map fun (id, position) =>
    (id, arguments[position]!)

/-- Why `structName` cannot be registered as a premise record, if it cannot. -/
def premiseRecordProblem? (structName : Name) : MetaM (Option MessageData) := do
  let environment ← getEnv
  unless isStructure environment structName do
    return some m!"{structName} is not a structure"
  if isClass environment structName then
    return some m!"{structName} is a class"
  if isPremiseRecord environment structName then
    return some m!"{structName} is already registered"
  let info ← getConstInfo structName
  if ← forallTelescopeReducing info.type fun _ sort => return sort.isProp then
    return some m!"{structName} is a proposition, which needs no \
      registration"
  return none

end Trust.Ledger
