module

public import Problib.Measure.Pi
public import Problib.Measure.StandardBorel.Pi

set_option autoImplicit false

namespace Problib.Measure.StandardBorel.Necessity

public section

/-- Product space of discrete Boolean spaces indexed by the real line. -/
@[expose] def booleanProduct : Space (Real.Carrier → Bool) :=
  Space.pi (fun _ : Real.Carrier => Space.discrete Bool)

/-- Every Boolean factor in the real-indexed product is standard Borel. -/
theorem boolean_factors_standardBorel (index : Real.Carrier) :
    Nonempty (StandardBorel ((fun _ : Real.Carrier => Space.discrete Bool) index)) := by
  refine ⟨ofNatInjection (fun value : Bool => if value then 1 else 0) ?_⟩
  intro left right equal
  cases left <;> cases right <;> simp_all

/-- Refutation: the real-indexed product of Boolean spaces cannot embed into
the real line by a Cantor diagonal argument. -/
theorem booleanProduct_not_standardBorel : ¬Nonempty (StandardBorel booleanProduct) := by
  rintro ⟨presentation⟩
  let embedding := presentation.embeddingReal
  let decode := embedding.retract (fun _ => false)
  let diagonal : Real.Carrier → Bool := fun seed => !(decode seed seed)
  let seed := embedding.function diagonal
  have recovered : decode seed = diagonal :=
    embedding.retract_forward (fun _ => false) diagonal
  have fixed : diagonal seed = !(diagonal seed) := by
    change Bool.not (decode seed seed) = Bool.not (diagonal seed)
    rw [recovered]
  cases value : diagonal seed <;> simp [value] at fixed

/-- Refutation: arbitrary products of standard-Borel spaces fail to be standard
Borel in general. -/
theorem arbitrary_product_closure_fails :
    (∀ index : Real.Carrier,
      Nonempty (StandardBorel ((fun _ : Real.Carrier => Space.discrete Bool) index))) ∧
      ¬Nonempty (StandardBorel booleanProduct) :=
  ⟨boolean_factors_standardBorel, booleanProduct_not_standardBorel⟩

/-- An empty-indexed product of spaces is standard Borel. -/
theorem empty_index_product_standardBorel :
    Nonempty (StandardBorel (Space.pi (fun _ : Empty => Space.discrete Empty))) := by
  refine ⟨piOfNatInjection (fun index => nomatch index) ?_ ?_⟩
  · intro left
    exact nomatch left
  · intro index
    exact nomatch index

/-- A countable product of empty spaces is standard Borel. -/
theorem countable_empty_product_standardBorel :
    Nonempty (StandardBorel (Space.pi (fun _ : Nat => Space.discrete Empty))) :=
  ⟨countableProduct (fun _ => ofEmpty (fun ⟨point⟩ => nomatch point))⟩

/-- The carrier of a countable product of empty spaces is empty. -/
theorem countable_empty_product_empty : ¬Nonempty (Nat → Empty) :=
  fun ⟨point⟩ => nomatch point 0

end

end Problib.Measure.StandardBorel.Necessity
