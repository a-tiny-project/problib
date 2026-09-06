namespace Foundations

universe u v w x

inductive Power (α : Type u) : Nat → Type u where
  | nil : Power α 0
  | cons {n : Nat} : α → Power α n → Power α (n + 1)
deriving Repr, DecidableEq

namespace Power

def map {α : Type u} {β : Type v} (transform : α → β) :
    {n : Nat} → Power α n → Power β n
  | 0, .nil => .nil
  | _ + 1, .cons head tail => .cons (transform head) (map transform tail)

def split {α : Type u} {β : Type v} :
    {n : Nat} → Power (α × β) n → Power α n × Power β n
  | 0, .nil => (.nil, .nil)
  | _ + 1, .cons head tail =>
      let rest := split tail
      (.cons head.1 rest.1, .cons head.2 rest.2)

def combine {α : Type u} {β : Type v} {n : Nat}
    (left : Power α n) (right : Power β n) : Power (α × β) n :=
  match left, right with
  | .nil, .nil => .nil
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      .cons (leftHead, rightHead) (combine leftTail rightTail)

theorem split_eq_maps {α : Type u} {β : Type v} {n : Nat}
    (values : Power (α × β) n) :
    split values = (map Prod.fst values, map Prod.snd values) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [split, map, ih]

def replicate {α : Type u} (value : α) : (n : Nat) → Power α n
  | 0 => .nil
  | n + 1 => .cons value (replicate value n)

def zipWith {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β → γ) {n : Nat}
    (left : Power α n) (right : Power β n) : Power γ n :=
  match left, right with
  | .nil, .nil => .nil
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      .cons (transform leftHead rightHead) (zipWith transform leftTail rightTail)

theorem zipWith_pair_eq_combine {α : Type u} {β : Type v} {n : Nat}
    (left : Power α n) (right : Power β n) :
    zipWith (fun leftValue rightValue => (leftValue, rightValue)) left right =
      combine left right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [zipWith, combine, ih]

@[simp] theorem map_id {α : Type u} {n : Nat} (values : Power α n) :
    map (fun value => value) values = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, ih]

theorem zipWith_commute {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β → γ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    zipWith transform left right =
      zipWith (fun rightValue leftValue => transform leftValue rightValue) right left := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [zipWith, ih]

@[simp] theorem map_map {α : Type u} {β : Type v} {γ : Type w}
    (second : β → γ) (first : α → β) {n : Nat} (values : Power α n) :
    map second (map first values) = map (fun value => second (first value)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, ih]

@[simp] theorem map_fst_map {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β × γ) {n : Nat} (values : Power α n) :
    map Prod.fst (map transform values) = map (fun value => (transform value).1) values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, ih]

@[simp] theorem map_snd_map {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β × γ) {n : Nat} (values : Power α n) :
    map Prod.snd (map transform values) = map (fun value => (transform value).2) values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, ih]

@[simp] theorem map_const {α : Type u} {β : Type v}
    (value : β) {n : Nat} (values : Power α n) :
    map (fun _ => value) values = replicate value n := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, replicate, ih]

@[simp] theorem map_replicate {α : Type u} {β : Type v}
    (transform : α → β) (value : α) (n : Nat) :
    map transform (replicate value n) = replicate (transform value) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [map, replicate, ih]

@[simp] theorem split_combine {α : Type u} {β : Type v} {n : Nat}
    (left : Power α n) (right : Power β n) :
    split (combine left right) = (left, right) := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail =>
          simp [combine, split, ih]

@[simp] theorem split_zipWith {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (leftMap : α → β → γ) (rightMap : α → β → δ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    split (zipWith (fun leftValue rightValue =>
      (leftMap leftValue rightValue, rightMap leftValue rightValue)) left right) =
      (zipWith leftMap left right, zipWith rightMap left right) := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [split, zipWith, ih]

@[simp] theorem combine_split {α : Type u} {β : Type v} {n : Nat}
    (values : Power (α × β) n) :
    combine (split values).1 (split values).2 = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [split, combine, ih]

@[simp] theorem map_zipWith {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (after : γ → δ) (transform : α → β → γ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    map after (zipWith transform left right) =
      zipWith (fun leftValue rightValue => after (transform leftValue rightValue))
        left right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [map, zipWith, ih]

@[simp] theorem zipWith_map_left
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (transform : β → γ → δ) (before : α → β) {n : Nat}
    (left : Power α n) (right : Power γ n) :
    zipWith transform (map before left) right =
      zipWith (fun leftValue rightValue => transform (before leftValue) rightValue)
        left right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [map, zipWith, ih]

@[simp] theorem zipWith_map_dependent_apply
    {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β → γ) {n : Nat}
    (functions : Power (α → β) n) (values : Power α n) :
    zipWith (fun function value => function value)
        (map (fun function value => transform value (function value)) functions)
        values =
      zipWith transform values
        (zipWith (fun function value => function value) functions values) := by
  induction functions with
  | nil =>
      cases values
      rfl
  | cons function rest ih =>
      cases values with
      | cons value restValues => simp [map, zipWith, ih]

@[simp] theorem zipWith_maps
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (transform : β → γ → δ) (leftMap : α → β) (rightMap : α → γ)
    {n : Nat} (values : Power α n) :
    zipWith transform (map leftMap values) (map rightMap values) =
      map (fun value => transform (leftMap value) (rightMap value)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [map, zipWith, ih]

@[simp] theorem map_zipWith_pair_left {α : Type u} {β : Type v} {n : Nat}
    (left : Power α n) (right : Power β n) :
    map Prod.fst (zipWith (fun leftValue rightValue => (leftValue, rightValue)) left right) =
      left := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [map, zipWith, ih]

@[simp] theorem map_zipWith_pair_right {α : Type u} {β : Type v} {n : Nat}
    (left : Power α n) (right : Power β n) :
    map Prod.snd (zipWith (fun leftValue rightValue => (leftValue, rightValue)) left right) =
      right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [map, zipWith, ih]

@[simp] theorem zipWith_replicate_left {α : Type u} {β : Type v}
    (transform : α → β) {n : Nat} (values : Power α n) :
    zipWith (fun function value => function value) (replicate transform n) values =
      map transform values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [zipWith, replicate, map, ih]

@[simp] theorem zipWith_replicate_binary
    {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β → γ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    zipWith (fun function value => function value)
        (zipWith (fun function value => function value)
          (replicate transform n) left)
        right =
      zipWith transform left right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [zipWith, replicate]

@[simp] theorem zipWith_ignore_right {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → γ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    zipWith (fun leftValue _ => transform leftValue) left right = map transform left := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [zipWith, map, ih]

@[simp] theorem zipWith_ignore_left {α : Type u} {β : Type v} {γ : Type w}
    (transform : β → γ) {n : Nat}
    (left : Power α n) (right : Power β n) :
    zipWith (fun _ rightValue => transform rightValue) left right = map transform right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail ih =>
      cases right with
      | cons rightHead rightTail => simp [zipWith, map, ih]

theorem eq_replicate {α : Type u} [Subsingleton α] {n : Nat}
    (values : Power α n) (value : α) : values = replicate value n := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headEqual : head = value := Subsingleton.elim _ _
      subst head
      simp [replicate, ih]

def fromPair {α : Type u} {n : Nat} : α × Power α n → Power α (n + 1)
  | (head, tail) => .cons head tail

def toPair {α : Type u} {n : Nat} : Power α (n + 1) → α × Power α n
  | .cons head tail => (head, tail)

@[simp] theorem toPair_fromPair {α : Type u} {n : Nat} (value : α × Power α n) :
    toPair (fromPair value) = value := by
  cases value
  rfl

@[simp] theorem fromPair_toPair {α : Type u} {n : Nat} (value : Power α (n + 1)) :
    fromPair (toPair value) = value := by
  cases value
  rfl

end Power

end Foundations
