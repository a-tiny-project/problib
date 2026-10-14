module
public import Problib.Measure.Measurability
public import Problib.Measure.Space.List
public import Problib.Measure.Space.Countable
public import Problib.Measure.Product.Countable
public import Problib.Countable.Bijection

set_option autoImplicit false
namespace Problib.Measure
public section
universe u v w
variable {α : Type u}

private def positionCode : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.succ (Countable.Pair.encode (head, positionCode tail))

private theorem positionCode_injective : Function.Injective positionCode := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons head tail => cases equal
  | cons head tail induction =>
      intro right equal
      cases right with
      | nil => cases equal
      | cons other rest =>
          have paired := Countable.Pair.encode_injective (Nat.succ.inj equal)
          have heads : head = other := congrArg Prod.fst paired
          have tails : tail = rest := induction (congrArg Prod.snd paired)
          simp only [heads, tails]

private theorem position_singleton_measurable (positions : List Nat) :
    (Space.list (Space.discrete Nat)).Measurable
      (fun other => other = positions) := by
  induction positions with
  | nil =>
      have measured := ListSpace.length_measurable (Space.discrete Nat)
        (set := fun length => length = 0) trivial
      have equal : Set.preimage List.length (fun length => length = 0) =
          (fun other : List Nat => other = []) := by
        funext other
        cases other <;> simp [Set.preimage]
      rw [equal] at measured
      exact measured

  | cons head tail induction =>
      let element := Space.discrete Nat
      let lists := Space.list element
      have selected :
          (Space.sum (Space.discrete Unit) (Space.product element lists)).Measurable
            (fun choice => match choice with
              | .inl _ => False
              | .inr (value, rest) => value = head ∧ rest = tail) := by
        constructor
        · exact (Space.discrete Unit).empty
        · have measured := Space.product_set_measurable element lists
            (leftSet := fun value => value = head) trivial induction
          have equal : Set.product (fun value : Nat => value = head)
              (fun rest : List Nat => rest = tail) =
              Set.preimage Sum.inr (fun choice : Sum Unit (Nat × List Nat) =>
                match choice with
                | .inl _ => False
                | .inr (value, rest) => value = head ∧ rest = tail) := by
            funext input
            cases input
            rfl
          rw [equal] at measured
          exact measured
      have measured := ListSpace.view_measurable element selected
      have equal : Set.preimage ListSpace.view (fun choice : Sum Unit (Nat × List Nat) =>
          match choice with
          | .inl _ => False
          | .inr (value, rest) => value = head ∧ rest = tail) =
          (fun other : List Nat => other = head :: tail) := by
        funext other
        cases other with
        | nil => simp [Set.preimage, ListSpace.view]
        | cons value rest =>
            simp [Set.preimage, ListSpace.view]
      rw [equal] at measured
      exact measured

private theorem position_discrete_measurable :
    MeasurableMap (Space.list (Space.discrete Nat))
      (Space.discrete (List Nat)) id := by
  apply MeasurableMap.to_discrete
  intro region
  classical
  have pieces (positions : List Nat) :
      (Space.list (Space.discrete Nat)).Measurable
        (fun other => other = positions ∧ region positions) := by
    by_cases member : region positions
    · have equal : (fun other : List Nat => other = positions ∧ region positions) =
          (fun other => other = positions) := by
        funext other
        simp [member]
      rw [equal]
      exact position_singleton_measurable positions
    · have equal : (fun other : List Nat => other = positions ∧ region positions) =
          Set.empty := by
        funext other
        simp [member, Set.empty]
      rw [equal]
      exact (Space.list (Space.discrete Nat)).empty
  have union := Space.i_union_of_nat_injection
    (Space.list (Space.discrete Nat)) positionCode positionCode_injective
    (fun positions other => other = positions ∧ region positions) pieces
  have equal : Set.preimage id region =
      (fun other => ∃ positions, other = positions ∧ region positions) := by
    funext other
    apply propext
    constructor
    · intro member
      exact ⟨other, rfl, member⟩
    · rintro ⟨positions, rfl, member⟩
      exact member
  rw [equal]
  exact union

/-- Every map out of finite lists of discrete positions is measurable. -/
public theorem positions_map_measurable {β : Type u} (target : Space β)
    (function : List Nat → β) :
    MeasurableMap (Space.list (Space.discrete Nat)) target function :=
  MeasurableMap.comp (MeasurableMap.from_discrete target function)
    position_discrete_measurable

/-- A map whose first argument is a finite list of discrete positions is jointly
measurable when each fixed list gives a measurable map. -/
public theorem positions_uncurry_measurable {β : Type v} {γ : Type w} {source : Space β}
    {target : Space γ} {function : List Nat → β → γ}
    (measurable : ∀ positions, MeasurableMap source target (function positions)) :
    MeasurableMap (Space.product (Space.list (Space.discrete Nat)) source) target
      (fun input => function input.1 input.2) :=
  MeasurableMap.comp
    (MeasurableMap.uncurry_of_countable_first positionCode positionCode_injective
      measurable)
    (Space.product_map position_discrete_measurable (MeasurableMap.identity source))

/-- A set whose first coordinate is a finite list of discrete positions is
measurable when each fixed list gives a measurable section. -/
public theorem positions_uncurry_set_measurable {β : Type v} {source : Space β}
    {sets : List Nat → Set β} (measurable : ∀ positions, source.Measurable (sets positions)) :
    (Space.product (Space.list (Space.discrete Nat)) source).Measurable
      (fun input => sets input.1 input.2) := by
  let rectangles := fun positions => Set.product (fun other : List Nat => other = positions)
    (sets positions)
  have rectangleMeasurable : ∀ positions,
      (Space.product (Space.list (Space.discrete Nat)) source).Measurable
        (rectangles positions) :=
    fun positions => Space.product_set_measurable _ _
      (position_singleton_measurable positions) (measurable positions)
  have equal : (fun input : List Nat × β => sets input.1 input.2) =
      (fun input => ∃ positions, rectangles positions input) := by
    apply Set.ext
    intro input
    constructor
    · intro member
      exact ⟨input.1, rfl, member⟩
    · rintro ⟨positions, same, member⟩
      change sets positions input.2 at member
      change sets input.1 input.2
      rw [same]
      exact member
  rw [equal]
  exact (Space.product (Space.list (Space.discrete Nat)) source).i_union_of_nat_injection
    positionCode positionCode_injective rectangles rectangleMeasurable

/-- The result is the remaining list and elements removed in removal order. -/
@[expose] public def removeAll : List Nat → List α → List α × List α
  | [], values => (values, [])
  | index :: rest, values =>
      match values[index]? with
      | none => removeAll rest values
      | some value =>
          let result := removeAll rest (values.eraseIdx index)
          (result.1, value :: result.2)

/-- Insert elements at successive positions, consuming one position per element. -/
@[expose] public def insertAll : List Nat → List α → List α → List α
  | [], _, values => values
  | _, [], values => values
  | index :: rest, value :: inserted, values =>
      insertAll rest inserted (values.insertIdx index value)

@[expose] public def ValidRemoval : List Nat → Nat → Prop
  | [], _ => True
  | index :: rest, length => index < length ∧ ValidRemoval rest (length - 1)

@[expose] public def ValidInsertion : List Nat → Nat → Prop
  | [], _ => True
  | index :: rest, length => index ≤ length ∧ ValidInsertion rest (length + 1)

/-- Single deletion followed by insertion restores a list when the index exists. -/
public theorem insertIdx_eraseIdx_self {values : List α} {index : Nat}
    (below : index < values.length) :
    (values.eraseIdx index).insertIdx index values[index] = values := by
  induction values generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ below)
  | cons head tail induction =>
      cases index with
      | zero => rfl
      | succ index =>
          have short : index < tail.length := Nat.lt_of_succ_lt_succ below
          simpa only [List.eraseIdx_cons_succ, List.insertIdx_succ_cons,
            List.getElem_cons_succ] using
            congrArg (List.cons head) (induction short)

private theorem removeAll_cons {values : List α} {index : Nat}
    (rest : List Nat) (below : index < values.length) :
    removeAll (index :: rest) values =
      let result := removeAll rest (values.eraseIdx index)
      (result.1, values[index] :: result.2) := by
  simp only [removeAll, List.getElem?_eq_getElem below]

public theorem removeAll_length {positions : List Nat} {values : List α}
    (valid : ValidRemoval positions values.length) :
    (removeAll positions values).1.length = values.length - positions.length ∧
      (removeAll positions values).2.length = positions.length := by
  induction positions generalizing values with
  | nil =>
      simp [removeAll]
  | cons index rest induction =>
      have below := valid.1
      have tailValid : ValidRemoval rest (values.eraseIdx index).length := by
        simpa only [List.length_eraseIdx_of_lt below] using valid.2
      have tailLength := induction (values := values.eraseIdx index) tailValid
      rw [removeAll_cons rest below]
      constructor
      · dsimp
        rw [tailLength.1, List.length_eraseIdx_of_lt below]
        omega
      · dsimp
        rw [tailLength.2]

private theorem insertAll_append {first second : List Nat}
    {inserted extra values : List α} (same : inserted.length = first.length) :
    insertAll (first ++ second) (inserted ++ extra) values =
      insertAll second extra (insertAll first inserted values) := by
  induction first generalizing inserted values with
  | nil =>
      cases inserted with
      | nil => rfl
      | cons head tail => cases same
  | cons index rest induction =>
      cases inserted with
      | nil => cases same
      | cons head tail =>
          have smaller : tail.length = rest.length := Nat.succ.inj same
          simpa only [List.cons_append, insertAll] using
            induction (inserted := tail) (values := values.insertIdx index head)
              smaller

/-- Reverse the removal schedule and reinsert each removed value. -/
public theorem insertAll_removeAll {positions : List Nat} {values : List α}
    (valid : ValidRemoval positions values.length) :
    insertAll positions.reverse (removeAll positions values).2.reverse
      (removeAll positions values).1 = values := by
  induction positions generalizing values with
  | nil => rfl
  | cons index rest induction =>
      have below := valid.1
      have tailValid : ValidRemoval rest (values.eraseIdx index).length := by
        simpa only [List.length_eraseIdx_of_lt below] using valid.2
      have tailLength := (removeAll_length (values := values.eraseIdx index) tailValid).2
      have restored := induction (values := values.eraseIdx index) tailValid
      rw [removeAll_cons rest below]
      dsimp
      rw [List.reverse_cons, List.reverse_cons]
      rw [insertAll_append (first := rest.reverse)
        (inserted := (removeAll rest (values.eraseIdx index)).2.reverse)
        (by simpa only [List.length_reverse] using tailLength)]
      rw [restored]
      exact insertIdx_eraseIdx_self below

private theorem removeAll_append (first second : List Nat) (values : List α) :
    removeAll (first ++ second) values =
      let initial := removeAll first values
      let final := removeAll second initial.1
      (final.1, initial.2 ++ final.2) := by
  induction first generalizing values with
  | nil => simp [removeAll]
  | cons index rest induction =>
      cases selected : values[index]? with
      | none => simp [removeAll, selected, induction]
      | some value => simp [removeAll, selected, induction, List.cons_append]

private theorem removeAll_single_insert {values : List α} {index : Nat}
    (value : α) (included : index ≤ values.length) :
    removeAll [index] (values.insertIdx index value) = (values, [value]) := by
  simp [removeAll, List.getElem?_insertIdx_self, included,
    List.eraseIdx_insertIdx_self]

/-- Reversing a valid insertion schedule recovers its source and inputs. -/
public theorem removeAll_insertAll {positions : List Nat}
    {inserted values : List α} (valid : ValidInsertion positions values.length)
    (length : inserted.length = positions.length) :
    removeAll positions.reverse (insertAll positions inserted values) =
      (values, inserted.reverse) := by
  induction positions generalizing inserted values with
  | nil =>
      cases inserted with
      | nil => rfl
      | cons head tail => cases length
  | cons index rest induction =>
      cases inserted with
      | nil => cases length
      | cons value remainder =>
          have included := valid.1
          have tailValid : ValidInsertion rest
              (values.insertIdx index value).length := by
            simpa only [List.length_insertIdx_of_le_length included value] using valid.2
          have tailLength : remainder.length = rest.length := Nat.succ.inj length
          have restored := induction (inserted := remainder)
            (values := values.insertIdx index value) tailValid tailLength
          simp only [List.reverse_cons, insertAll]
          rw [removeAll_append, restored]
          dsimp
          rw [removeAll_single_insert value included]

/-- Select a measurable optional list coordinate at a discrete index. -/
public theorem coordinate_at_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.list element) (Space.discrete Nat))
      (Space.sum (Space.discrete Unit) element)
      (fun input => ListSpace.coordinate input.2 input.1) := by
  apply MeasurableMap.countable_piecewise
    (partition := fun input : List α × Nat => input.2)
    (branches := fun index input => ListSpace.coordinate index input.1)
  · intro index
    exact Space.second_measurable (Space.list element) (Space.discrete Nat)
      (Space.discrete_measurable (fun value : Nat => value = index))
  · intro index
    measurability [ListSpace.coordinate_measurable element index]

private theorem coordinate_eraseIdx (values : List α) (index coordinate : Nat) :
    ListSpace.coordinate coordinate (values.eraseIdx index) =
      if index ≤ coordinate then ListSpace.coordinate (coordinate + 1) values
      else ListSpace.coordinate coordinate values := by
  induction values generalizing index coordinate with
  | nil => simp [ListSpace.coordinate]
  | cons head tail induction =>
      cases index with
      | zero =>
          cases coordinate <;> rfl
      | succ index =>
          cases coordinate with
          | zero => rfl
          | succ coordinate =>
              simpa only [List.eraseIdx_cons_succ, ListSpace.coordinate,
                Nat.succ_le_succ_iff, Nat.succ_eq_add_one]
                using induction index coordinate

/-- Erasing a discretely selected list position is measurable. -/
public theorem eraseIdx_measurable (element : Space α) :
    MeasurableMap (Space.product (Space.list element) (Space.discrete Nat))
      (Space.list element) (fun input => input.1.eraseIdx input.2) := by
  let source := Space.product (Space.list element) (Space.discrete Nat)
  have partition (index : Nat) :
      source.Measurable (fun input : List α × Nat => input.2 = index) :=
    Space.second_measurable _ _
      (Space.discrete_measurable (fun value : Nat => value = index))
  apply ListSpace.measurable
  · have branches : ∀ index, MeasurableMap source (Space.discrete Nat)
        (fun input : List α × Nat =>
          if index < input.1.length then input.1.length - 1
          else input.1.length) := by
      intro index
      exact MeasurableMap.comp
        (MeasurableMap.from_discrete (Space.discrete Nat)
          (fun length => if index < length then length - 1 else length))
        (MeasurableMap.comp (ListSpace.length_measurable element)
          (Space.first_measurable _ _))
    have measured : MeasurableMap source (Space.discrete Nat)
        (fun input : List α × Nat =>
          if input.2 < input.1.length then input.1.length - 1
          else input.1.length) :=
      MeasurableMap.countable_piecewise partition branches
    simp only [List.length_eraseIdx]
    measurability
  · intro coordinate
    have branches : ∀ index, MeasurableMap source
        (Space.sum (Space.discrete Unit) element)
        (fun input : List α × Nat =>
          if index ≤ coordinate then
            ListSpace.coordinate (coordinate + 1) input.1
          else ListSpace.coordinate coordinate input.1) := by
      intro index
      split
      · measurability [ListSpace.coordinate_measurable element (coordinate + 1)]
      · measurability [ListSpace.coordinate_measurable element coordinate]
    have measured : MeasurableMap source
        (Space.sum (Space.discrete Unit) element)
        (fun input : List α × Nat =>
          if input.2 ≤ coordinate then
            ListSpace.coordinate (coordinate + 1) input.1
          else ListSpace.coordinate coordinate input.1) :=
      MeasurableMap.countable_piecewise partition branches
    have equal : (fun input : List α × Nat =>
        ListSpace.coordinate coordinate (input.1.eraseIdx input.2)) =
        (fun input => if input.2 ≤ coordinate then
          ListSpace.coordinate (coordinate + 1) input.1
          else ListSpace.coordinate coordinate input.1) := by
      funext input
      exact coordinate_eraseIdx input.1 input.2 coordinate
    rw [equal]
    measurability

private def optionCoordinate : Option α → Sum Unit α
  | none => .inl ()
  | some value => .inr value

private theorem coordinate_eq_option (values : List α) (coordinate : Nat) :
    ListSpace.coordinate coordinate values = optionCoordinate values[coordinate]? := by
  induction values generalizing coordinate with
  | nil => cases coordinate <;> rfl
  | cons head tail induction =>
      cases coordinate with
      | zero => rfl
      | succ coordinate => exact induction coordinate

private theorem removeAll_fixed_measurable (element : Space α)
    (positions : List Nat) :
    MeasurableMap (Space.list element)
      (Space.product (Space.list element) (Space.list element))
      (removeAll positions) := by
  induction positions with
  | nil =>
      exact Space.pair_measurable
        (MeasurableMap.identity (Space.list element))
        (MeasurableMap.constant (Space.list element) (Space.list element) [])
  | cons index rest induction =>
      have equal :
          (fun values : List α => Sum.elim
            (fun input : Unit × List α => removeAll rest input.2)
            (fun input : α × List α =>
              let output := removeAll rest (input.2.eraseIdx index)
              (output.1, input.1 :: output.2))
            (Sum.elim (fun empty => Sum.inl (empty, values))
              (fun value => Sum.inr (value, values))
              (ListSpace.coordinate index values))) =
            removeAll (index :: rest) := by
        funext values
        rw [coordinate_eq_option]
        cases selected : values[index]? <;>
          simp only [optionCoordinate, Sum.elim, removeAll, selected]
      rw [← equal]
      measurability [ListSpace.coordinate_measurable element index,
        ListSpace.cons_measurable element, eraseIdx_measurable element]

/-- Successive deletion is jointly measurable in its schedule and source list. -/
public theorem removeAll_measurable (element : Space α) :
    MeasurableMap
      (Space.product (Space.list (Space.discrete Nat)) (Space.list element))
      (Space.product (Space.list element) (Space.list element))
      (fun input => removeAll input.1 input.2) := by
  have discrete : MeasurableMap
      (Space.product (Space.list (Space.discrete Nat)) (Space.list element))
      (Space.product (Space.discrete (List Nat)) (Space.list element))
      (fun input => input) := by
    exact Space.product_map position_discrete_measurable
      (MeasurableMap.identity (Space.list element))
  measurability [MeasurableMap.uncurry_of_countable_first positionCode
    positionCode_injective (removeAll_fixed_measurable element)]

private theorem coordinate_insertIdx (values : List α) (index coordinate : Nat)
    (value : α) :
    ListSpace.coordinate coordinate (values.insertIdx index value) =
      if coordinate < index then ListSpace.coordinate coordinate values
      else if coordinate = index then
        if coordinate ≤ values.length then Sum.inr value else Sum.inl ()
      else ListSpace.coordinate (coordinate - 1) values := by
  rw [coordinate_eq_option, List.getElem?_insertIdx]
  by_cases before : coordinate < index
  · simp only [ite_eq_left before, coordinate_eq_option]
  · simp only [ite_eq_right before]
    by_cases same : coordinate = index
    · simp only [ite_eq_left same]
      split <;> rfl
    · simp only [ite_eq_right same, coordinate_eq_option]

/-- Inserting an element at a discrete list position is measurable. -/
public theorem insertIdx_measurable (element : Space α) :
    MeasurableMap
      (Space.product (Space.product (Space.list element) (Space.discrete Nat)) element)
      (Space.list element)
      (fun input => input.1.1.insertIdx input.1.2 input.2) := by
  let parameter := Space.product (Space.list element) (Space.discrete Nat)
  let source := Space.product parameter element
  have indexMap : MeasurableMap source (Space.discrete Nat)
      (fun input : (List α × Nat) × α => input.1.2) := by
    measurability
  have lengthMap : MeasurableMap source (Space.discrete Nat)
      (fun input : (List α × Nat) × α => input.1.1.length) := by
    measurability [ListSpace.length_measurable element]
  have valueMap : MeasurableMap source element
      (fun input : (List α × Nat) × α => input.2) :=
    Space.second_measurable _ _
  have coordinateMap (coordinate : Nat) :
      MeasurableMap source (Space.sum (Space.discrete Unit) element)
        (fun input : (List α × Nat) × α =>
          ListSpace.coordinate coordinate input.1.1) := by
    measurability [ListSpace.coordinate_measurable element coordinate]
  have partitionIndex (index : Nat) :
      source.Measurable
        (fun input : (List α × Nat) × α => input.1.2 = index) :=
    indexMap (Space.discrete_measurable (fun value : Nat => value = index))
  have partitionLength (length : Nat) :
      source.Measurable
        (fun input : (List α × Nat) × α => input.1.1.length = length) :=
    lengthMap (Space.discrete_measurable (fun value : Nat => value = length))
  apply ListSpace.measurable
  · have branches : ∀ index, MeasurableMap source (Space.discrete Nat)
        (fun input : (List α × Nat) × α =>
          if index ≤ input.1.1.length then input.1.1.length + 1
          else input.1.1.length) := by
      intro index
      exact MeasurableMap.comp
        (MeasurableMap.from_discrete (Space.discrete Nat)
          (fun length => if index ≤ length then length + 1 else length))
        lengthMap
    have measured : MeasurableMap source (Space.discrete Nat)
        (fun input : (List α × Nat) × α =>
          if input.1.2 ≤ input.1.1.length then input.1.1.length + 1
          else input.1.1.length) :=
      MeasurableMap.countable_piecewise partitionIndex branches
    simp only [List.length_insertIdx]
    measurability
  · intro coordinate
    have branches : ∀ index, MeasurableMap source
        (Space.sum (Space.discrete Unit) element)
        (fun input : (List α × Nat) × α =>
          if coordinate < index then
            ListSpace.coordinate coordinate input.1.1
          else if coordinate = index then
            if coordinate ≤ input.1.1.length then Sum.inr input.2
            else Sum.inl ()
          else ListSpace.coordinate (coordinate - 1) input.1.1) := by
      intro index
      by_cases before : coordinate < index
      · simpa only [ite_eq_left before] using coordinateMap coordinate
      · by_cases same : coordinate = index
        · have innerBranches : ∀ length, MeasurableMap source
              (Space.sum (Space.discrete Unit) element)
              (fun input : (List α × Nat) × α =>
                if coordinate ≤ length then Sum.inr input.2 else Sum.inl ()) := by
            intro length
            by_cases included : coordinate ≤ length
            · simpa only [ite_eq_left included] using
                MeasurableMap.comp
                  (MeasurableMap.inr (Space.discrete Unit) element) valueMap
            · simpa only [ite_eq_right included] using
                MeasurableMap.constant source
                  (Space.sum (Space.discrete Unit) element) (Sum.inl ())
          have inner : MeasurableMap source
              (Space.sum (Space.discrete Unit) element)
              (fun input : (List α × Nat) × α =>
                if coordinate ≤ input.1.1.length then Sum.inr input.2
                else Sum.inl ()) :=
            MeasurableMap.countable_piecewise partitionLength innerBranches
          simpa only [ite_eq_right before, ite_eq_left same] using inner
        · simpa only [ite_eq_right before, ite_eq_right same] using
            coordinateMap (coordinate - 1)
    have measured : MeasurableMap source
        (Space.sum (Space.discrete Unit) element)
        (fun input : (List α × Nat) × α =>
          if coordinate < input.1.2 then
            ListSpace.coordinate coordinate input.1.1
          else if coordinate = input.1.2 then
            if coordinate ≤ input.1.1.length then Sum.inr input.2
            else Sum.inl ()
          else ListSpace.coordinate (coordinate - 1) input.1.1) :=
      MeasurableMap.countable_piecewise partitionIndex branches
    have equal :
        (fun input : (List α × Nat) × α =>
          ListSpace.coordinate coordinate
            (input.1.1.insertIdx input.1.2 input.2)) =
        (fun input =>
          if coordinate < input.1.2 then
            ListSpace.coordinate coordinate input.1.1
          else if coordinate = input.1.2 then
            if coordinate ≤ input.1.1.length then Sum.inr input.2
            else Sum.inl ()
          else ListSpace.coordinate (coordinate - 1) input.1.1) := by
      funext input
      exact coordinate_insertIdx input.1.1 input.1.2 coordinate input.2
    rw [equal]
    measurability

private theorem insertAll_fixed_measurable (element : Space α)
    (positions : List Nat) :
    MeasurableMap
      (Space.product (Space.list element) (Space.list element))
      (Space.list element)
      (fun input => insertAll positions input.1 input.2) := by
  induction positions with
  | nil => exact Space.second_measurable _ _
  | cons index rest induction =>
      have equal :
          (fun input : List α × List α => Sum.elim
            (fun absent : Unit × List α => absent.2)
            (fun present : (α × List α) × List α =>
              insertAll rest present.1.2
                (present.2.insertIdx index present.1.1))
            (Sum.elim (fun empty => Sum.inl (empty, input.2))
              (fun part => Sum.inr (part, input.2))
              (ListSpace.view input.1))) =
          (fun input => insertAll (index :: rest) input.1 input.2) := by
        funext input
        cases input.1 <;> rfl
      rw [← equal]
      measurability [ListSpace.view_measurable element, insertIdx_measurable element]

/-- Successive insertion is jointly measurable in its schedule, inputs, and source. -/
public theorem insertAll_measurable (element : Space α) :
    MeasurableMap
      (Space.product
        (Space.product (Space.list (Space.discrete Nat)) (Space.list element))
        (Space.list element))
      (Space.list element)
      (fun input => insertAll input.1.1 input.1.2 input.2) := by
  let positions := Space.list (Space.discrete Nat)
  let lists := Space.list element
  have grouped : MeasurableMap
      (Space.product (Space.product positions lists) lists)
      (Space.product (Space.discrete (List Nat)) (Space.product lists lists))
      (fun input => (input.1.1, (input.1.2, input.2))) :=
    MeasurableMap.comp
      (Space.product_map position_discrete_measurable
        (MeasurableMap.identity (Space.product lists lists)))
      (Space.associate_measurable positions lists lists)
  measurability [MeasurableMap.comp (MeasurableMap.uncurry_of_countable_first
    positionCode positionCode_injective (insertAll_fixed_measurable element)) grouped]

/-- Insertion at a fixed position is measurable in the list and the element. -/
public theorem insert_at_measurable (element : Space α) (index : Nat) :
    MeasurableMap (Space.product (Space.list element) element) (Space.list element)
      (fun input => input.1.insertIdx index input.2) := by
  measurability [insertIdx_measurable element]

private theorem foldr_insert_last (values : List α) :
    values.foldr (fun head rest => rest.insertIdx rest.length head) [] =
      values.reverse := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      rw [List.foldr_cons, induction, List.insertIdx_length_self,
        List.reverse_cons]

/-- Reversal is measurable on finite lists. -/
public theorem reverse_measurable (element : Space α) :
    MeasurableMap (Space.list element) (Space.list element) List.reverse := by
  have step : MeasurableMap
      (Space.product element (Space.product (Space.list element) (Space.discrete Unit)))
      (Space.list element)
      (fun input => input.2.1.insertIdx input.2.1.length input.1) := by
    measurability [insertIdx_measurable element, ListSpace.length_measurable element]
  have folded : MeasurableMap
      (Space.product (Space.list element) (Space.discrete Unit)) (Space.list element)
      (fun input => input.1.foldr (fun head rest =>
        (fun input : α × (List α × Unit) =>
          input.2.1.insertIdx input.2.1.length input.1) (head, rest, input.2))
        ((fun _ : Unit => ([] : List α)) input.2)) :=
    ListSpace.fold_measurable (MeasurableMap.constant _ _ []) step
  have paired : MeasurableMap (Space.list element)
      (Space.product (Space.list element) (Space.discrete Unit))
      (fun values => (values, ())) := by
    measurability
  have composed : MeasurableMap (Space.list element) (Space.list element)
      (fun values : List α =>
        values.foldr (fun head rest => rest.insertIdx rest.length head) []) :=
    MeasurableMap.comp folded paired
  have equal : (fun values : List α =>
      values.foldr (fun head rest => rest.insertIdx rest.length head) []) =
      List.reverse := funext foldr_insert_last
  rw [← equal]
  measurability

private theorem valid_insertion_append_single {positions : List Nat}
    {index count : Nat} :
    ValidInsertion (positions ++ [index]) count ↔
      ValidInsertion positions count ∧ index ≤ count + positions.length := by
  induction positions generalizing count with
  | nil => simp [ValidInsertion]
  | cons first rest induction =>
      simp only [List.cons_append, ValidInsertion, induction, List.length_cons]
      constructor
      · rintro ⟨below, valid, last⟩
        exact ⟨⟨below, valid⟩, by omega⟩
      · rintro ⟨⟨below, valid⟩, last⟩
        exact ⟨below, valid, by omega⟩

/-- A removal schedule read backwards is an insertion schedule into the
remaining list. -/
public theorem valid_insertion_reverse {positions : List Nat} {count : Nat}
    (valid : ValidRemoval positions (count + positions.length)) :
    ValidInsertion positions.reverse count := by
  induction positions with
  | nil => trivial
  | cons index rest induction =>
      rcases valid with ⟨below, restValid⟩
      have shorter : count + (rest.length + 1) - 1 = count + rest.length := by omega
      rw [List.length_cons, shorter] at restValid
      rw [List.reverse_cons, valid_insertion_append_single]
      refine ⟨induction restValid, ?_⟩
      rw [List.length_reverse]
      rw [List.length_cons] at below
      omega

/-- Successive insertion at fixed positions is measurable in the source list and
the inserted elements. -/
public theorem insertAll_at_measurable (element : Space α) (positions : List Nat) :
    MeasurableMap (Space.product (Space.list element) (Space.list element))
      (Space.list element) (fun input => insertAll positions input.2 input.1) := by
  measurability [insertAll_measurable element]

/-- Successive removal at fixed positions is measurable. -/
public theorem removeAll_at_measurable (element : Space α) (positions : List Nat) :
    MeasurableMap (Space.list element)
      (Space.product (Space.list element) (Space.list element))
      (removeAll positions) := by
  measurability [removeAll_measurable element]

end
end Problib.Measure
