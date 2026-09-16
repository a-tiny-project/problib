import Init.Data.Rat.Lemmas

namespace Foundations.Linear.Rational

universe u v

def listSum {α : Type u} (values : List α) (term : α → Rat) : Rat :=
  match values with
  | [] => 0
  | value :: rest => term value + listSum rest term

theorem listSum_congr {α : Type u} (values : List α) {left right : α → Rat}
    (equal : ∀ value ∈ values, left value = right value) :
    listSum values left = listSum values right := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [listSum, listSum, equal head (by simp)]
      apply congrArg (fun rest => right head + rest)
      exact ih fun value member => equal value (by simp [member])

theorem listSum_zero {α : Type u} (values : List α) :
    listSum values (fun _ => 0) = 0 := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [listSum, ih, Rat.zero_add]

theorem listSum_add {α : Type u} (values : List α) (left right : α → Rat) :
    listSum values (fun value => left value + right value) =
      listSum values left + listSum values right := by
  induction values with
  | nil =>
      change (0 : Rat) = 0 + 0
      rw [Rat.zero_add]
  | cons head tail ih =>
      rw [listSum, listSum, listSum, ih]
      calc
        left head + right head + (listSum tail left + listSum tail right) =
            left head + (right head + (listSum tail left + listSum tail right)) :=
          Rat.add_assoc _ _ _
        _ = left head + (listSum tail left + (right head + listSum tail right)) := by
          rw [Rat.add_left_comm (right head) (listSum tail left) (listSum tail right)]
        _ = (left head + listSum tail left) + (right head + listSum tail right) :=
          (Rat.add_assoc _ _ _).symm

theorem listSum_scale_left {α : Type u} (values : List α)
    (constant : Rat) (term : α → Rat) :
    listSum values (fun value => constant * term value) = constant * listSum values term := by
  induction values with
  | nil =>
      change (0 : Rat) = constant * 0
      rw [Rat.mul_zero]
  | cons head tail ih =>
      rw [listSum, listSum, ih, Rat.mul_add]

theorem listSum_scale_right {α : Type u} (values : List α)
    (term : α → Rat) (constant : Rat) :
    listSum values (fun value => term value * constant) = listSum values term * constant := by
  calc
    listSum values (fun value => term value * constant) =
        listSum values (fun value => constant * term value) := by
          apply listSum_congr
          intro value member
          exact Rat.mul_comm _ _
    _ = constant * listSum values term := listSum_scale_left values constant term
    _ = listSum values term * constant := Rat.mul_comm _ _

theorem listSum_indicator {α : Type u} [DecidableEq α]
    (values : List α) (target : α) (term : α → Rat)
    (nodup : values.Nodup) (present : target ∈ values) :
    listSum values (fun value => if value = target then term value else 0) = term target := by
  induction values with
  | nil => cases present
  | cons head tail ih =>
      have facts := List.nodup_cons.1 nodup
      by_cases equal : head = target
      · subst head
        have tailZero : listSum tail (fun value => if value = target then term value else 0) = 0 := by
          calc
            listSum tail (fun value => if value = target then term value else 0) =
                listSum tail (fun _ => 0) := by
                  apply listSum_congr
                  intro value member
                  have unequal : value ≠ target := by
                    intro valueEqual
                    subst value
                    exact facts.1 member
                  simp [unequal]
            _ = 0 := listSum_zero tail
        rw [listSum, if_pos rfl, tailZero, Rat.add_zero]
      · have targetUnequal : target ≠ head := by
          intro reverseEqual
          exact equal reverseEqual.symm
        have tailPresent : target ∈ tail := (List.mem_cons.1 present).resolve_left targetUnequal
        rw [listSum, if_neg equal, Rat.zero_add, ih facts.2 tailPresent]

theorem listSum_swap {α : Type u} {β : Type v}
    (leftValues : List α) (rightValues : List β) (term : α → β → Rat) :
    listSum leftValues (fun left => listSum rightValues (term left)) =
      listSum rightValues (fun right => listSum leftValues fun left => term left right) := by
  induction leftValues with
  | nil =>
      rw [listSum]
      exact (listSum_zero rightValues).symm
  | cons head tail ih =>
      rw [listSum, ih]
      change listSum rightValues (term head) +
          listSum rightValues (fun right => listSum tail fun left => term left right) =
        listSum rightValues (fun right => term head right +
          listSum tail fun left => term left right)
      exact (listSum_add rightValues (term head)
        (fun right => listSum tail fun left => term left right)).symm

def finSum {n : Nat} (term : Fin n → Rat) : Rat :=
  listSum (List.finRange n) term

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      apply List.nodup_cons.2
      constructor
      · intro member
        have existsEqual := List.mem_map.1 member
        cases existsEqual with
        | intro value facts => exact Fin.succ_ne_zero value facts.2
      · apply List.Pairwise.map
          (R := fun left right : Fin n => left ≠ right)
          (S := fun left right : Fin (n + 1) => left ≠ right)
          Fin.succ
        · intro left right unequal equal
          exact unequal (Fin.succ_inj.mp equal)
        · exact ih

theorem finSum_congr {n : Nat} {left right : Fin n → Rat}
    (equal : ∀ index, left index = right index) : finSum left = finSum right :=
  listSum_congr (List.finRange n) fun value _ => equal value

theorem finSum_zero {n : Nat} : finSum (fun _ : Fin n => 0) = 0 :=
  listSum_zero (List.finRange n)

theorem finSum_one_dimension (term : Fin 1 → Rat) :
    finSum term = term ⟨0, by decide⟩ := by
  rw [finSum, List.finRange_succ, List.finRange_zero]
  change term ⟨0, by decide⟩ + 0 = term ⟨0, by decide⟩
  rw [Rat.add_zero]

theorem finSum_indicator {n : Nat} (target : Fin n) (term : Fin n → Rat) :
    finSum (fun index => if index = target then term index else 0) = term target :=
  listSum_indicator (List.finRange n) target term (finRange_nodup n) (List.mem_finRange target)

theorem finSum_add {n : Nat} (left right : Fin n → Rat) :
    finSum (fun index => left index + right index) = finSum left + finSum right :=
  listSum_add (List.finRange n) left right

theorem finSum_scale_left {n : Nat} (constant : Rat) (term : Fin n → Rat) :
    finSum (fun index => constant * term index) = constant * finSum term :=
  listSum_scale_left (List.finRange n) constant term

theorem finSum_scale_right {n : Nat} (term : Fin n → Rat) (constant : Rat) :
    finSum (fun index => term index * constant) = finSum term * constant :=
  listSum_scale_right (List.finRange n) term constant

theorem finSum_swap {rows columns : Nat} (term : Fin rows → Fin columns → Rat) :
    finSum (fun row => finSum fun column => term row column) =
      finSum (fun column => finSum fun row => term row column) :=
  listSum_swap (List.finRange rows) (List.finRange columns) term

end Foundations.Linear.Rational
