module

public import Foundations.Real.Series.Basis

set_option autoImplicit false

namespace Foundations.Real.ENNReal

/-- Any nonempty predicate of extended nonnegative real numbers contains a
countable sequence whose supremum matches the set supremum.

The proof selects sequence terms through the countable rational basis and
handles infinite suprema without topological machinery. -/
public theorem existsSequenceSupremum {values : ENNReal → Prop}
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
  refine ⟨sequence, members, leAntisymm (iSupLe (fun index => leSupremum (members index))) ?_⟩
  apply supremumLe
  intro value member
  by_cases included : le value (iSup sequence)
  · exact included
  · have separated : lt (iSup sequence) value :=
      ⟨(leTotal (iSup sequence) value).resolve_right included, included⟩
    rcases existsRationalBasisBetween separated with ⟨index, below, above⟩
    have chosen := (Classical.choose_spec (select index)).2 ⟨value, member, above⟩
    exact False.elim (below.right (leTrans chosen.left (leISup sequence index)))

end Foundations.Real.ENNReal
