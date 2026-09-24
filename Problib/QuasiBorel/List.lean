module

public import Problib.QuasiBorel.Sum
public import Problib.QuasiBorel.CartesianClosed

set_option autoImplicit false

namespace Problib.QuasiBorel
public section
universe u v
variable {Ω : Type u} {source : Source Ω}

/-- Finite list random elements, closed under reparameterization and countable
measurable gluing. Cons combines correlated head and tail random elements. -/
inductive ListRandom (element : Space.{u, v} source) :
    (Ω → List element.Carrier) → Prop where
  | nil : ListRandom element (fun _ => [])
  | cons {head tail} : element.Random head → ListRandom element tail →
      ListRandom element (fun seed => head seed :: tail seed)
  | reparam {parameter random} : source.Measurable parameter →
      ListRandom element random → ListRandom element (fun seed => random (parameter seed))
  | piecewise {partition : Ω → Nat} {branches : Nat → Ω → List element.Carrier} :
      source.Partition partition → (∀ index, ListRandom element (branches index)) →
      ListRandom element (fun seed => branches (partition seed) seed)

namespace Space

@[expose] def list (element : Space.{u, v} source) : Space source where
  Carrier := List element.Carrier
  Random := ListRandom element
  constant := by
    intro values
    induction values with
    | nil => exact .nil
    | cons head tail induction => exact .cons (element.constant head) induction
  reparam := ListRandom.reparam
  piecewise := ListRandom.piecewise

@[expose] def listCons (element : Space.{u, v} source) :
    Hom (product element (list element)) (list element) where
  toFun := fun input => input.1 :: input.2
  map_random := fun accepted => .cons accepted.1 accepted.2

@[expose] def listView (element : Space.{u, v} source) :
    Hom (list element) (sum (terminal source) (product element (list element))) where
  toFun := fun values => match values with
    | [] => .inl ()
    | head :: tail => .inr (head, tail)
  map_random := by
    intro random accepted
    induction accepted with
    | nil => exact SumRandom.inl trivial
    | cons head tail _ => exact SumRandom.inr ⟨head, tail⟩
    | reparam measurable _ induction => exact SumRandom.reparam measurable induction
    | piecewise measurable _ induction => exact SumRandom.piecewise measurable induction

/-- Fold one finite list into a morphism that retains its captured parameter. -/
@[expose] def listFoldAt {element result parameter : Space source}
    (initial : Hom parameter result)
    (step : Hom (product element (product result parameter)) result) :
    List element.Carrier → Hom parameter result
  | [] => initial
  | head :: tail => Hom.comp step
      (pair (Hom.constant _ _ head) (pair (listFoldAt initial step tail) (Hom.identity _)))

@[simp] theorem listFoldAt_apply {element result parameter : Space source}
    (initial : Hom parameter result)
    (step : Hom (product element (product result parameter)) result)
    (values : List element.Carrier) (captured : parameter.Carrier) :
    listFoldAt initial step values captured =
      values.foldr (fun head rest => step (head, rest, captured)) (initial captured) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      change step (head, listFoldAt initial step tail captured, captured) = _
      rw [induction]
      rfl

/-- A fold may share arbitrary parameters with its list and algebra maps. -/
@[expose] def listFold {element result parameter : Space source}
    (initial : Hom parameter result)
    (step : Hom (product element (product result parameter)) result) :
    Hom (product (list element) parameter) result :=
  uncurry {
    toFun := listFoldAt initial step
    map_random := by
      intro random accepted
      induction accepted with
      | nil => exact (exponential parameter result).constant initial
      | cons head tail induction =>
          intro randomPair valid
          exact step.map_random ⟨element.reparam valid.1 head, induction valid, valid.2⟩
      | @reparam mapping random measurable _ induction =>
          exact (exponential parameter result).reparam
            (random := fun seed => listFoldAt initial step (random seed)) measurable induction
      | piecewise measurable _ induction =>
          exact (exponential parameter result).piecewise measurable induction
  }

@[simp] theorem listFold_apply {element result parameter : Space source}
    (initial : Hom parameter result)
    (step : Hom (product element (product result parameter)) result)
    (values : List element.Carrier) (captured : parameter.Carrier) :
    listFold initial step (values, captured) =
      values.foldr (fun head rest => step (head, rest, captured)) (initial captured) :=
  listFoldAt_apply initial step values captured

end Space
end
end Problib.QuasiBorel
