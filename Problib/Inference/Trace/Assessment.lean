namespace Problib.Inference.Trace

universe u v w

structure ZeroScore (Score : Type w) where
  zero : Score

/--
An assessor either consumes its whole query and reports its density, or leaves
a remainder and certifies that the query has the explicit zero score.
-/
structure RemainderSpecification
    {Trace : Type u} {Result : Type v} {Score : Type w}
    (scores : ZeroScore Score) (empty : Trace)
    (density : Trace → Score) (result : Trace → Result)
    (assess : Trace → Result × (Score × Trace)) : Prop where
  resultCorrect : ∀ query, (assess query).1 = result query
  consumedScore : ∀ query,
    (assess query).2.2 = empty → (assess query).2.1 = density query
  remainderDensityZero : ∀ query,
    (assess query).2.2 ≠ empty → density query = scores.zero

def wrappedScore {Trace : Type u} {Result : Type v} {Score : Type w}
    [DecidableEq Trace] (scores : ZeroScore Score) (empty : Trace)
    (assess : Trace → Result × (Score × Trace)) : Trace → Score :=
  fun query =>
    if (assess query).2.2 = empty then (assess query).2.1 else scores.zero

theorem RemainderSpecification.wrappedScore_correct
    {Trace : Type u} {Result : Type v} {Score : Type w}
    [DecidableEq Trace] {scores : ZeroScore Score} {empty : Trace}
    {density : Trace → Score} {result : Trace → Result}
    {assess : Trace → Result × (Score × Trace)}
    (specification :
      RemainderSpecification scores empty density result assess)
    (query : Trace) :
    wrappedScore scores empty assess query = density query := by
  unfold wrappedScore
  by_cases consumed : (assess query).2.2 = empty
  · rw [if_pos consumed]
    exact specification.consumedScore query consumed
  · rw [if_neg consumed]
    exact (specification.remainderDensityZero query consumed).symm

theorem RemainderSpecification.of_wrappedScore
    {Trace : Type u} {Result : Type v} {Score : Type w}
    [DecidableEq Trace] {scores : ZeroScore Score} {empty : Trace}
    {density : Trace → Score} {result : Trace → Result}
    {assess : Trace → Result × (Score × Trace)}
    (resultCorrect : ∀ query, (assess query).1 = result query)
    (correct : ∀ query,
      wrappedScore scores empty assess query = density query) :
    RemainderSpecification scores empty density result assess := by
  refine {
    resultCorrect := resultCorrect
    consumedScore := ?_
    remainderDensityZero := ?_
  }
  · intro query consumed
    have scoreCorrect := correct query
    unfold wrappedScore at scoreCorrect
    rw [if_pos consumed] at scoreCorrect
    exact scoreCorrect
  · intro query remainder
    have scoreCorrect := correct query
    unfold wrappedScore at scoreCorrect
    rw [if_neg remainder] at scoreCorrect
    exact scoreCorrect.symm

theorem RemainderSpecification.consumes_of_nonzero
    {Trace : Type u} {Result : Type v} {Score : Type w}
    [DecidableEq Trace]
    {scores : ZeroScore Score} {empty : Trace}
    {density : Trace → Score} {result : Trace → Result}
    {assess : Trace → Result × (Score × Trace)}
    (specification :
      RemainderSpecification scores empty density result assess)
    {query : Trace} (nonzero : density query ≠ scores.zero) :
    (assess query).2.2 = empty := by
  by_cases consumed : (assess query).2.2 = empty
  · exact consumed
  · exact False.elim
      (nonzero (specification.remainderDensityZero query consumed))

end Problib.Inference.Trace
