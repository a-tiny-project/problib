module

public import Problib.Measure.Memo.Binary
public import Problib.Measure.Memo.Product
public import Problib.Countable.Bijection

set_option autoImplicit false

/-!
# Independent uniform seeds from one fair table

Cantor pairing splits one fair table into countably many rows. The rows are
independent fair tables, and the binary value of each row is uniform, so the
row values form a sequence of independent uniform seeds drawn from a single
uniform seed.
-/

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Measure.Real

/-- The rows of a table under Cantor pairing. -/
@[expose] def rows (table : Table) (row : Nat) : Table :=
  fun column => table (Countable.Pair.encode (row, column))

theorem rows_measurable : MeasurableMap tableSpace (Space.pi fun _ : Nat => tableSpace) rows :=
  Space.pi_measurable fun row =>
    Space.pi_reindex (fun _ : Nat => Space.discrete Bool)
      fun column => Countable.Pair.encode (row, column)

/-- Independent uniform seeds: the binary values of the rows of one fair
table. -/
@[expose] noncomputable def uniformSequence : Measure (Space.pi fun _ : Nat => unitBorel) :=
  ((law fun _ => fair).map rows rows_measurable).map (fun tables row => binaryValue (tables row))
    (Space.pi_map fun _ => binaryValue_measurable)

private theorem pair_injective (row column other position : Nat)
    (same : Countable.Pair.encode (row, column) = Countable.Pair.encode (other, position)) :
    row = other ∧ column = position :=
  Prod.mk.inj (Countable.Pair.encode_injective same)

/-- Every row of the fair table law is the fair table law. -/
theorem law_fair_row (row : Nat) :
    (law fun _ => fair).map (fun table column => table (Countable.Pair.encode (row, column)))
        (Space.pi_reindex (fun _ : Nat => Space.discrete Bool)
          fun column => Countable.Pair.encode (row, column)) =
      law fun _ => fair := by
  have marginal : ∀ index, (law fun _ => fair).map (fun table => table index)
      (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) index) =
        (law fun _ => fair).map (fun table => table 0)
          (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) 0) :=
    fun index => law_marginal_congr _ rfl
  have whole := (law_isProduct fun _ => fair).congr_laws marginal
  have reindexed := ((law_isProduct fun _ => fair).reindex
    (fun column => Countable.Pair.encode (row, column))
    (fun _ _ same => (pair_injective _ _ _ _ same).2)).congr_laws fun column => marginal _
  exact reindexed.ext whole

/-- The rows of the fair table law are independent fair tables. -/
theorem rows_isProduct :
    Pi.IsProduct ((law fun _ => fair).map rows rows_measurable) fun _ => law fun _ => fair :=
  ((law_isProduct fun _ => fair).blocks (fun row column => Countable.Pair.encode (row, column))
    pair_injective).congr_laws law_fair_row

/-- The uniform sequence is a product of uniform laws: its seeds are
independent and uniform. -/
theorem uniformSequence_isProduct : Pi.IsProduct uniformSequence fun _ => uniform01 :=
  (rows_isProduct.map (fun _ => binaryValue) fun _ => binaryValue_measurable).congr_laws
    fun _ => law_fair_binaryValue

theorem uniformSequence_probability : uniformSequence.IsProbability :=
  uniformSequence_isProduct.probability

end
end Problib.Measure.Memo
