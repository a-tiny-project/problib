module

public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Any nonempty predicate of extended nonnegative real numbers contains a
countable sequence whose supremum matches the set supremum.

The proof selects sequence terms through the countable rational basis and
handles infinite suprema without topological machinery. -/
public theorem exists_sequence_supremum {values : ENNReal → Prop}
    (nonempty : ∃ value, values value) :
    ∃ sequence : Nat → ENNReal, (∀ index, values (sequence index)) ∧
      iSup sequence = supremum values := by
  classical
  rcases nonempty with ⟨seed, seedMember⟩
  have select : ∀ index, ∃ value, values value ∧
      ((∃ upper, values upper ∧ lt (rationalBasis index) upper) →
        lt (rationalBasis index) value) := by
    intro index
    by_cases available : ∃ upper, values upper ∧ lt (rationalBasis index) upper
    · rcases available with ⟨upper, member, greater⟩
      exact ⟨upper, member, fun _ => greater⟩
    · exact ⟨seed, seedMember, fun witness => False.elim (available witness)⟩
  let sequence := fun index => Classical.choose (select index)
  have members : ∀ index, values (sequence index) :=
    fun index => (Classical.choose_spec (select index)).1
  refine ⟨sequence, members, le_antisymm (iSup_le (fun index => le_supremum (members index))) ?_⟩
  apply supremum_le
  intro value member
  by_cases included : le value (iSup sequence)
  · exact included
  · have separated : lt (iSup sequence) value :=
      ⟨(le_total (iSup sequence) value).resolve_right included, included⟩
    rcases exists_rationalBasis_between separated with ⟨index, below, above⟩
    have chosen := (Classical.choose_spec (select index)).2 ⟨value, member, above⟩
    exact False.elim (below.right (le_trans chosen.left (le_iSup sequence index)))

end Problib.Real.ENNReal
