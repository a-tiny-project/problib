import Problib.Algebra.Sum
import Problib.Real.Nonnegative.Embedding
import Problib.Linear.Rational.Sum

/-! Clamping embedded rationals at zero commutes with summing nonnegative ones. -/

namespace Problib.Real.NNReal

open Problib.Linear.Rational (listSum listSum_nonneg)

theorem listSum_ofReal_ofRat {ι : Type} (indices : List ι) (term : ι → Rat)
    (nonnegative : ∀ index ∈ indices, 0 ≤ term index) :
    additiveLaws.listSum
        (indices.map fun index => ofReal (Construction.Dedekind.selection.ofRat (term index))) =
      ofReal (Construction.Dedekind.selection.ofRat (listSum indices term)) := by
  induction indices with
  | nil =>
      show zero = _
      rw [ofReal_ofRat_of_nonnegative
        (show (0 : Rat) ≤ listSum ([] : List ι) term from Rat.le_refl)]
      exact ofRat_zero.symm
  | cons index rest previous =>
      have restNonnegative := fun other member => nonnegative other (List.mem_cons_of_mem index member)
      show add (ofReal (Construction.Dedekind.selection.ofRat (term index))) (additiveLaws.listSum _) = _
      rw [previous restNonnegative,
        ofReal_ofRat_of_nonnegative (nonnegative index List.mem_cons_self),
        ofReal_ofRat_of_nonnegative (listSum_nonneg rest term restNonnegative),
        ofReal_ofRat_of_nonnegative (listSum_nonneg (index :: rest) term nonnegative)]
      exact (ofRat_add _ _ _ _).symm

end Problib.Real.NNReal
