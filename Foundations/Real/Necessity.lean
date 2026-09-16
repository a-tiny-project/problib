module

public import Foundations.Real.Interface

namespace Foundations.Real.Necessity

private def closedLower (value : Rat) : Prop :=
  value ≤ 0

private theorem closedLowerNonempty : ∃ value, closedLower value := by
  exact ⟨0, Rat.le_refl⟩

private theorem closedLowerProper : ∃ value, ¬closedLower value := by
  refine ⟨1, ?_⟩
  change ¬(1 : Rat) ≤ 0
  decide

private theorem closedLowerDownward :
    ∀ {left right}, left < right → closedLower right → closedLower left := by
  intro left right leftRight rightMember
  exact Rat.le_trans (Rat.le_of_lt leftRight) rightMember

private theorem closedLowerHasGreatest :
    ¬∀ {value}, closedLower value →
      ∃ greater, closedLower greater ∧ value < greater := by
  intro noGreatest
  rcases noGreatest Rat.le_refl with ⟨greater, greaterMember, zeroGreater⟩
  exact (Rat.not_lt.mpr greaterMember) zeroGreater

public theorem noGreatestPremiseNecessary :
    ∃ lower : Rat → Prop,
      (∃ value, lower value) ∧
      (∃ value, ¬lower value) ∧
      (∀ {left right}, left < right → lower right → lower left) ∧
      ¬∀ {value}, lower value →
        ∃ greater, lower greater ∧ value < greater := by
  exact ⟨closedLower, closedLowerNonempty, closedLowerProper,
    closedLowerDownward, closedLowerHasGreatest⟩

public theorem orderEmbeddingNeedNotPreserveAddition :
    ∃ embedding : Rat → Rat,
      (∀ left right, embedding left ≤ embedding right ↔ left ≤ right) ∧
      ¬∀ left right,
        embedding (left + right) = embedding left + embedding right := by
  refine ⟨fun value => value + 1, ?_, ?_⟩
  · intro left right
    exact Rat.add_le_add_right
  · intro preserves
    have impossible := preserves 0 0
    simp only [Rat.zero_add] at impossible
    have zeroOne : (0 : Rat) < 1 := by decide
    have oneTwo : (1 : Rat) < 1 + 1 := by
      have translated :=
        (Rat.add_lt_add_left (a := 0) (b := 1) (c := 1)).mpr zeroOne
      rw [Rat.add_zero] at translated
      exact translated
    have selfLess : (1 : Rat) < 1 := by
      calc
        (1 : Rat) < 1 + 1 := oneTwo
        _ = 1 := impossible.symm
    exact Rat.lt_irrefl selfLess

public theorem additiveGroupAndOrderNeedNotTranslateMonotonically :
    ∃ group : Foundations.Algebra.AdditiveCommutativeGroupLaws Bool,
      ∃ order : Foundations.Algebra.LinearOrderLaws Bool,
        ¬Foundations.Algebra.TranslationMonotone
          Bool order.le group.add := by
  let group : Foundations.Algebra.AdditiveCommutativeGroupLaws Bool := {
    zero := false
    add := Bool.xor
    neg := fun value => value
    add_comm := by
      intro left right
      cases left <;> cases right <;> rfl
    add_assoc := by
      intro left middle right
      cases left <;> cases middle <;> cases right <;> rfl
    add_zero := by
      intro value
      cases value <;> rfl
    add_neg := by
      intro value
      cases value <;> rfl
  }
  let order : Foundations.Algebra.LinearOrderLaws Bool := {
    le := fun left right => left = false ∨ right = true
    refl := by
      intro value
      cases value <;> simp
    trans := by
      intro left middle right leftMiddle middleRight
      cases left <;> cases middle <;> cases right <;> simp_all
    antisymm := by
      intro left right leftRight rightLeft
      cases left <;> cases right <;> simp_all
    total := by
      intro left right
      cases left <;> cases right <;> simp
  }
  refine ⟨group, order, ?_⟩
  intro monotone
  have included : order.le false true := by
    exact Or.inl rfl
  have shifted := monotone.add_le_add_right included true
  simp [group, order] at shifted

public theorem multiplicationPreservationNeedNotPreserveOne :
    ∃ map : Rat → Rat,
      (∀ left right, map (left * right) = map left * map right) ∧
      map 1 ≠ 1 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro left right
    exact (Rat.zero_mul 0).symm
  · decide

end Foundations.Real.Necessity
