module

public import Init

set_option autoImplicit false

namespace Problib.Relation
public section
universe u v

/-- Lift a relation to finite lists with corresponding elements and equal length. -/
inductive ListLift {α : Type u} {β : Type v} (relation : α → β → Prop) :
    List α → List β → Prop where
  | nil : ListLift relation [] []
  | cons {head other tail rest} : relation head other → ListLift relation tail rest →
      ListLift relation (head :: tail) (other :: rest)

/-- The indices `0, …, n - 1` of `List.finRange n` are pairwise distinct. -/
theorem List.finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
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

end
end Problib.Relation
