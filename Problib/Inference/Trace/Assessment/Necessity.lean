import Problib.Inference.Trace.Assessment

namespace Problib.Inference.Trace.Assessment.Necessity

def naturalZeroScore : Problib.Inference.Trace.ZeroScore Nat :=
  ⟨0⟩

def leftoverDensity (_ : Bool) : Nat :=
  0

def leftoverResult (_ : Bool) : PUnit :=
  PUnit.unit

def leftoverAssess : Bool → PUnit × (Nat × Bool)
  | false => (PUnit.unit, (0, false))
  | true => (PUnit.unit, (1, true))

theorem leftover_assessor_satisfies_specification :
    Problib.Inference.Trace.RemainderSpecification naturalZeroScore false
      leftoverDensity leftoverResult leftoverAssess := by
  refine {
    resultCorrect := ?_
    consumedScore := ?_
    remainderDensityZero := ?_
  }
  · intro query
    cases query <;> rfl
  · intro query consumed
    cases query
    · rfl
    · simp [leftoverAssess] at consumed
  · intro query remainder
    rfl

theorem remainder_specification_allows_nonzero_leftover_score :
    Problib.Inference.Trace.RemainderSpecification naturalZeroScore false
        leftoverDensity leftoverResult leftoverAssess ∧
      (leftoverAssess true).2.2 ≠ false ∧
      (leftoverAssess true).2.1 ≠ naturalZeroScore.zero := by
  exact ⟨leftover_assessor_satisfies_specification, by decide, by decide⟩

theorem raw_leftover_score_breaks_density_composition :
    (leftoverAssess true).2.1 * 1 ≠ leftoverDensity true := by
  decide

end Problib.Inference.Trace.Assessment.Necessity
