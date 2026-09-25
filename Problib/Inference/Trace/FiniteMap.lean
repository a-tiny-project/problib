import Problib.Inference.Trace.Resource

namespace Problib.Inference.Trace.FiniteMap

universe u v

abbrev Raw (Key : Type u) (Value : Type v) := Key → Option Value

abbrev Grade (Key : Type u) := Key → Bool

def grade {Key : Type u} {Value : Type v} (trace : Raw Key Value) : Grade Key :=
  fun key => (trace key).isSome

def Carrier (Key : Type u) (Value : Type v) (traceGrade : Grade Key) :=
  { trace : Raw Key Value // grade trace = traceGrade }

def Compatible {Key : Type u} (left right : Grade Key) : Prop :=
  ∀ key, left key = false ∨ right key = false

def appendGrade {Key : Type u} (left right : Grade Key) : Grade Key :=
  fun key => left key || right key

def appendRaw {Key : Type u} {Value : Type v}
    (left right : Raw Key Value) : Raw Key Value :=
  fun key =>
    match left key with
    | some value => some value
    | none => right key

def append {Key : Type u} {Value : Type v} {left right : Grade Key}
    (_compatible : Compatible left right)
    (leftTrace : Carrier Key Value left)
    (rightTrace : Carrier Key Value right) :
    Carrier Key Value (appendGrade left right) := by
  refine ⟨appendRaw leftTrace.1 rightTrace.1, ?_⟩
  funext key
  have leftGrade := congrFun leftTrace.2 key
  have rightGrade := congrFun rightTrace.2 key
  cases leftValue : leftTrace.1 key <;>
    cases rightValue : rightTrace.1 key <;>
      simp [grade, leftValue] at leftGrade <;>
        simp [grade, rightValue] at rightGrade <;>
          simp [grade, appendRaw, appendGrade, leftValue, rightValue,
            leftGrade, rightGrade]

def resource (Key : Type u) (Value : Type v) :
    Problib.Inference.Trace.Resource (Grade Key) (Carrier Key Value) where
  Compatible := Compatible
  appendGrade := fun {left right} _ => appendGrade left right
  append := append

structure Packed (Key : Type u) (Value : Type v) where
  traceGrade : Grade Key
  trace : Carrier Key Value traceGrade

def pack {Key : Type u} {Value : Type v}
    (trace : Raw Key Value) : Packed Key Value :=
  ⟨grade trace, ⟨trace, rfl⟩⟩

def restrict {Key : Type u} {Value : Type v}
    (traceGrade : Grade Key) (trace : Raw Key Value) : Raw Key Value :=
  fun key => if traceGrade key then trace key else none

def split {Key : Type u} {Value : Type v} {left right : Grade Key}
    (_compatible : Compatible left right)
    (trace : Carrier Key Value (appendGrade left right)) :
    Carrier Key Value left × Carrier Key Value right := by
  have leftCarrier : Carrier Key Value left := by
    refine ⟨restrict left trace.1, ?_⟩
    funext key
    have combinedGrade := congrFun trace.2 key
    cases leftAtKey : left key <;> cases rightAtKey : right key <;>
      cases traceAtKey : trace.1 key <;>
        simp [grade, restrict, appendGrade, leftAtKey, rightAtKey,
          traceAtKey] at combinedGrade ⊢
  have rightCarrier : Carrier Key Value right := by
    refine ⟨restrict right trace.1, ?_⟩
    funext key
    have combinedGrade := congrFun trace.2 key
    cases leftAtKey : left key <;> cases rightAtKey : right key <;>
      cases traceAtKey : trace.1 key <;>
        simp [grade, restrict, appendGrade, leftAtKey, rightAtKey,
          traceAtKey] at combinedGrade ⊢
  exact (leftCarrier, rightCarrier)

theorem split_append {Key : Type u} {Value : Type v}
    {left right : Grade Key} (compatible : Compatible left right)
    (leftTrace : Carrier Key Value left)
    (rightTrace : Carrier Key Value right) :
    split compatible (append compatible leftTrace rightTrace) =
      (leftTrace, rightTrace) := by
  apply Prod.ext <;> apply Subtype.ext <;> funext key
  · have leftGrade := congrFun leftTrace.2 key
    cases leftAtKey : leftTrace.1 key <;>
      simp [grade, leftAtKey] at leftGrade <;>
        simp [split, restrict, append, appendRaw, leftAtKey, leftGrade]
  · have rightGrade := congrFun rightTrace.2 key
    have leftGrade := congrFun leftTrace.2 key
    have disjoint := compatible key
    cases leftAtKey : leftTrace.1 key <;>
      cases rightAtKey : rightTrace.1 key <;>
        simp [grade, leftAtKey] at leftGrade <;>
          simp [grade, rightAtKey] at rightGrade <;>
            simp [split, restrict, append, appendRaw, leftAtKey,
              rightAtKey, leftGrade, rightGrade] at disjoint ⊢

theorem append_split {Key : Type u} {Value : Type v}
    {left right : Grade Key} (compatible : Compatible left right)
    (trace : Carrier Key Value (appendGrade left right)) :
    append compatible (split compatible trace).1 (split compatible trace).2 =
      trace := by
  apply Subtype.ext
  funext key
  have combinedGrade := congrFun trace.2 key
  have disjoint := compatible key
  cases leftAtKey : left key <;> cases rightAtKey : right key <;>
    cases traceAtKey : trace.1 key <;>
      simp [split, restrict, append, appendRaw, grade, appendGrade,
        leftAtKey, rightAtKey, traceAtKey] at combinedGrade disjoint ⊢

def lossless (Key : Type u) (Value : Type v) :
    Problib.Inference.Trace.Lossless (resource Key Value) where
  split := split
  split_append := split_append
  append_split := append_split

theorem compatible_iff_disjoint {Key : Type u} {Value : Type v}
    (left right : Raw Key Value) :
    Compatible (grade left) (grade right) ↔
      ∀ key leftValue rightValue,
        left key = some leftValue → right key = some rightValue → False := by
  constructor
  · intro compatible key leftValue rightValue leftPresent rightPresent
    rcases compatible key with leftAbsent | rightAbsent
    · simp [grade, leftPresent] at leftAbsent
    · simp [grade, rightPresent] at rightAbsent
  · intro disjoint key
    cases leftAtKey : left key with
    | none => exact Or.inl (by simp [grade, leftAtKey])
    | some leftValue =>
        cases rightAtKey : right key with
        | none => exact Or.inr (by simp [grade, rightAtKey])
        | some rightValue =>
            exact False.elim (disjoint key leftValue rightValue leftAtKey rightAtKey)

namespace Necessity

def singletonGrade : Grade PUnit := fun _ => true

theorem same_address_collision_blocks_composition :
    (resource PUnit Bool).Collision singletonGrade singletonGrade := by
  intro compatible
  rcases compatible PUnit.unit with leftAbsent | rightAbsent
  · simp [singletonGrade] at leftAbsent
  · simp [singletonGrade] at rightAbsent

def singletonRaw (value : Bool) : Raw PUnit Bool := fun _ => some value

theorem unsafe_append_forgets_right :
    appendRaw (singletonRaw false) (singletonRaw true) = singletonRaw false := by
  rfl

end Necessity

end Problib.Inference.Trace.FiniteMap
