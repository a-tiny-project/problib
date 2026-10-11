module
public import Problib.Measure.Space.Sigma
public import Problib.Measure.Space.List
public import Problib.Measure.Pi
public import Problib.Measure.Equivalence

set_option autoImplicit false
namespace Problib.Measure
public section
universe u v
variable {α : Type v}

/-- A countable family of measurable payload spaces. -/
public structure ConfigurationShapes where
  Shape : Type u
  code : Shape → Nat
  injective : Function.Injective code
  Payload : Shape → Type v
  space : ∀ shape, Space (Payload shape)

@[expose] public def finiteConfigurationSpace (shapes : ConfigurationShapes.{u,v}) :
    Space (Sigma shapes.Payload) := Space.sigma shapes.space

namespace ConfigurationShapes
/-- The countable family of finite coordinate powers of an element space. -/
@[expose, implicit_reducible] public def power {α : Type v} (element : Space α) : ConfigurationShapes.{0,v} where
  Shape := Nat
  code := id
  injective := fun _ _ equal => equal
  Payload := fun n => Fin n → α
  space := fun n => Space.pi (fun _ : Fin n => element)
end ConfigurationShapes

private theorem coordinate_option (values : List α) (coordinate : Nat) :
    ListSpace.coordinate coordinate values =
      match values[coordinate]? with
      | none => Sum.inl ()
      | some value => Sum.inr value := by
  induction values generalizing coordinate with
  | nil => cases coordinate <;> rfl
  | cons head tail induction =>
      cases coordinate with
      | zero => rfl
      | succ coordinate => exact induction coordinate

private theorem coordinate_ofFn {n : Nat} (point : Fin n → α)
    (coordinate : Nat) :
    ListSpace.coordinate coordinate (List.ofFn point) =
      if included : coordinate < n then Sum.inr (point ⟨coordinate, included⟩)
      else Sum.inl () := by
  rw [coordinate_option, List.getElem?_ofFn]
  by_cases included : coordinate < n
  · simp [included]
  · simp [included]

public theorem ofFn_measurable (element : Space α) (n : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin n => element))
      (Space.list element) List.ofFn := by
  apply ListSpace.measurable
  · have equal : (fun point : Fin n → α => (List.ofFn point).length) =
        (fun _ => n) := by
      funext point
      exact List.length_ofFn
    rw [equal]
    exact fun {set} =>
      MeasurableMap.constant (Space.pi (fun _ : Fin n => element))
        (Space.discrete Nat) n (set := set)
  · intro coordinate
    by_cases included : coordinate < n
    · have equal :
          (fun point : Fin n → α =>
            ListSpace.coordinate coordinate (List.ofFn point)) =
          (fun point => Sum.inr (point ⟨coordinate, included⟩)) := by
        funext point
        rw [coordinate_ofFn, dite_eq_left included]
      rw [equal]
      exact MeasurableMap.comp
        (MeasurableMap.inr (Space.discrete Unit) element)
        (Space.coordinate_measurable (fun _ : Fin n => element)
          ⟨coordinate, included⟩)
    · have equal :
          (fun point : Fin n → α =>
            ListSpace.coordinate coordinate (List.ofFn point)) =
          (fun _ => Sum.inl ()) := by
        funext point
        rw [coordinate_ofFn, dite_eq_right included]
      rw [equal]
      exact MeasurableMap.constant _
        (Space.sum (Space.discrete Unit) element) (Sum.inl ())

private theorem getD_measurable (element : Space α) (default : α)
    (coordinate : Nat) :
    MeasurableMap (Space.list element) element
      (fun values => values.getD coordinate default) := by
  have collapse : MeasurableMap
      (Space.sum (Space.discrete Unit) element) element
      (Sum.elim (fun _ => default) id) :=
    MeasurableMap.sum_elim
      (MeasurableMap.constant (Space.discrete Unit) element default)
      (MeasurableMap.identity element)
  have measured : MeasurableMap (Space.list element) element
      (fun values => Sum.elim (fun _ => default) id
        (ListSpace.coordinate coordinate values)) :=
    MeasurableMap.comp collapse (ListSpace.coordinate_measurable element coordinate)
  have equal :
      (fun values : List α => Sum.elim (fun _ => default) id
        (ListSpace.coordinate coordinate values)) =
      (fun values => values.getD coordinate default) := by
    funext values
    rw [coordinate_option, List.getD_eq_getElem?_getD]
    cases values[coordinate]? <;> rfl
  intro region regionMeasurable
  change (Space.list element).Measurable
    (Set.preimage (fun values => values.getD coordinate default) region)
  rw [← equal]
  exact measured regionMeasurable

private theorem list_tuple_measurable_of_nonempty (element : Space α)
    (nonempty : Nonempty α) :
    MeasurableMap (Space.list element)
      (finiteConfigurationSpace (ConfigurationShapes.power element))
      (fun values => ⟨values.length, fun index => values[index.val]⟩) := by
  change MeasurableMap (Space.list element)
    (Space.sigma (fun count : Nat => Space.pi (fun _ : Fin count => element)))
    (fun values => ⟨values.length, fun index : Fin values.length =>
      values[index.val]⟩)
  let default := Classical.choice nonempty
  have payload (count : Nat) : MeasurableMap (Space.list element)
      (Space.pi (fun _ : Fin count => element))
      (fun values index => values.getD index.val default) :=
    Space.pi_measurable (fun index => getD_measurable element default index.val)
  have measured : MeasurableMap (Space.list element)
      (Space.sigma (fun count : Nat => Space.pi (fun _ : Fin count => element)))
      (fun values => ⟨values.length, fun index : Fin values.length =>
        values.getD index.val default⟩) :=
    MeasurableMap.into_sigma (spaces :=
      (fun count : Nat => Space.pi (fun _ : Fin count => element))) id
      (fun _ _ equal => equal)
      (ListSpace.length_measurable element) payload
  have equal :
      (fun values : List α =>
        (⟨values.length, fun index : Fin values.length =>
          values.getD index.val default⟩ :
          Sigma fun count : Nat => Fin count → α)) =
      (fun values =>
        (⟨values.length, fun index : Fin values.length => values[index.val]⟩ :
          Sigma fun count : Nat => Fin count → α)) := by
    funext values
    congr 1
    funext index
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem index.isLt]
    rfl
  intro region regionMeasurable
  change (Space.list element).Measurable
    (Set.preimage (fun values : List α =>
      (⟨values.length, fun index : Fin values.length => values[index.val]⟩ :
        Sigma fun count : Nat => Fin count → α)) region)
  rw [← equal]
  exact measured regionMeasurable

public theorem list_tuple_measurable (element : Space α) :
    MeasurableMap (Space.list element)
      (finiteConfigurationSpace (ConfigurationShapes.power element))
      (fun values => ⟨values.length, fun index => values[index.val]⟩) := by
  change MeasurableMap (Space.list element)
    (Space.sigma (fun count : Nat => Space.pi (fun _ : Fin count => element)))
    (fun values => ⟨values.length, fun index : Fin values.length =>
      values[index.val]⟩)
  classical
  by_cases populated : Nonempty α
  · exact list_tuple_measurable_of_nonempty element populated
  · have allEmpty (values : List α) : values = [] := by
      cases values with
      | nil => rfl
      | cons head tail => exact False.elim (populated ⟨head⟩)
    have equal :
        (fun values : List α =>
          (⟨values.length, fun index : Fin values.length => values[index.val]⟩ :
            Sigma fun count : Nat => Fin count → α)) =
        (fun _ => (⟨0, Fin.elim0⟩ :
          Sigma fun count : Nat => Fin count → α)) := by
      funext values
      rw [allEmpty values]
      congr 1
      funext index
      exact Fin.elim0 index
    intro regionMeasurable
    change (Space.list element).Measurable
      (Set.preimage (fun values : List α =>
        (⟨values.length, fun index : Fin values.length => values[index.val]⟩ :
          Sigma fun count : Nat => Fin count → α)) _)
    rw [equal]
    exact MeasurableMap.constant _ _ (⟨0, Fin.elim0⟩ :
      Sigma fun count : Nat => Fin count → α) regionMeasurable

private theorem fin_cast_heq {first second : Nat} (equal : first = second)
    (coordinates : Fin second → α) :
    (fun index : Fin first => coordinates (Fin.cast equal index)) ≍ coordinates := by
  cases equal
  exact HEq.rfl

private theorem tuple_roundtrip (count : Nat) (coordinates : Fin count → α) :
    (⟨(List.ofFn coordinates).length,
      fun index : Fin (List.ofFn coordinates).length =>
        (List.ofFn coordinates)[index.val]⟩ :
      Sigma fun n : Nat => Fin n → α) = ⟨count, coordinates⟩ := by
  have length : (List.ofFn coordinates).length = count := List.length_ofFn
  apply Sigma.ext length
  change (fun index : Fin (List.ofFn coordinates).length =>
    (List.ofFn coordinates)[index.val]) ≍ coordinates
  have same : (fun index : Fin (List.ofFn coordinates).length =>
      (List.ofFn coordinates)[index.val]) =
      (fun index => coordinates (Fin.cast length index)) := by
    funext index
    rw [List.getElem_ofFn]
    congr 1
  rw [same]
  exact fin_cast_heq length coordinates

/-- Finite lists and the countable sum of their coordinate powers carry
equivalent measurable spaces. -/
@[expose] public noncomputable def listConfigurationEquivalence
    (element : Space α) :
    MeasurableEquivalence (Space.list element)
      (finiteConfigurationSpace (ConfigurationShapes.power element)) where
  forward values := ⟨values.length, fun index => values[index.val]⟩
  inverse point := List.ofFn point.2
  inverse_forward := by
    intro values
    exact List.ofFn_getElem
  forward_inverse := by
    intro point
    change (Sigma fun count : Nat => Fin count → α) at point
    cases point with
    | mk count coordinates => exact tuple_roundtrip count coordinates
  forward_measurable := list_tuple_measurable element
  inverse_measurable := by
    apply MeasurableMap.from_sigma_iff.mpr
    intro count
    exact ofFn_measurable element count

end
end Problib.Measure
