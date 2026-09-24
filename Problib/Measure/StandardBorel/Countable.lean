module

public import Problib.Measure.StandardBorel.Basic

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

open Problib.Real.Construction

universe u

private theorem reciprocal_successor_mem (index : Nat) :
    Real.unitSet
      (Dedekind.selection.ofRat ((Nat.succ index : Rat)⁻¹)) := by
  have positive : (0 : Rat) < (Nat.succ index : Rat) :=
    Rat.natCast_pos.mpr (Nat.zero_lt_succ index)
  constructor
  · rw [← Dedekind.ofRat_zero]
    exact (Dedekind.ofRat_le_iff _ _).mpr
      (Rat.le_of_lt (Rat.inv_pos.mpr positive))
  · rw [← Dedekind.ofRat_one]
    apply (Dedekind.ofRat_le_iff _ _).mpr
    apply Rat.le_of_mul_le_mul_right (c := (Nat.succ index : Rat))
      (hc := positive)
    rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt positive), Rat.one_mul]
    exact Rat.natCast_le_natCast.mpr (Nat.zero_lt_succ index)

/-- Reciprocal encoding of natural numbers into the unit interval. -/
public noncomputable def naturalCode (index : Nat) : Real.UnitInterval :=
  ⟨Dedekind.selection.ofRat ((Nat.succ index : Rat)⁻¹),
    reciprocal_successor_mem index⟩

/-- The reciprocal encoding of natural numbers into the unit interval is
injective. -/
public theorem naturalCode_injective : Function.Injective naturalCode := by
  intro left right equal
  have rational := Dedekind.ofRat_injective
    (congrArg (fun value : Real.UnitInterval => value.val) equal)
  have inverted := congrArg (fun value : Rat => value⁻¹) rational
  simp only [Rat.inv_inv] at inverted
  exact Nat.succ.inj (Rat.natCast_inj.mp inverted)

private theorem singleton_measurable (point : Real.UnitInterval) :
    Real.unitBorel.Measurable (fun value => value = point) := by
  have equal : (fun value : Real.UnitInterval => value = point) =
      Set.preimage Real.unitInclusion (Real.Icc point.val point.val) := by
    apply Set.ext
    intro value
    constructor
    · intro member
      subst value
      exact ⟨Dedekind.le_refl _, Dedekind.le_refl _⟩
    · intro member
      exact Subtype.ext (Dedekind.le_antisymm member.2 member.1)
  rw [equal]
  exact Real.unitInclusion_measurable (Real.measurable_icc _ _)

private theorem naturalCode_image_measurable {alpha : Type u}
    (code : alpha → Nat) (set : Set alpha) :
    Real.unitBorel.Measurable (Set.image (fun value => naturalCode (code value)) set) := by
  classical
  let pieces : Nat → Set Real.UnitInterval :=
    fun index point =>
      (∃ value, set value ∧ code value = index) ∧ naturalCode index = point
  have piecesMeasurable : ∀ index, Real.unitBorel.Measurable (pieces index) := by
    intro index
    by_cases member : ∃ value, set value ∧ code value = index
    · have equal : pieces index = (fun point => point = naturalCode index) := by
        apply Set.ext
        intro point
        exact ⟨fun included => included.2.symm,
          fun equal => ⟨member, equal.symm⟩⟩
      rw [equal]
      exact singleton_measurable _
    · have equal : pieces index = Set.empty := by
        apply Set.ext
        intro point
        exact ⟨fun included => member included.1, False.elim⟩
      rw [equal]
      exact Real.unitBorel.empty
  have equal : Set.image (fun value => naturalCode (code value)) set = Set.iUnion pieces := by
    apply Set.ext
    intro point
    constructor
    · rintro ⟨value, member, equal⟩
      exact ⟨code value, ⟨value, member, rfl⟩, equal⟩
    · rintro ⟨index, ⟨value, member, codeEqual⟩, pointEqual⟩
      exact ⟨value, member, (congrArg naturalCode codeEqual).trans pointEqual⟩
  rw [equal]
  exact Real.unitBorel.iUnion piecesMeasurable

/-- Discrete space with an injection into the natural numbers is standard
Borel. -/
public noncomputable def ofNatInjection {alpha : Type u}
    (code : alpha → Nat) (injective : Function.Injective code) :
    StandardBorel (Space.discrete alpha) := by
  let range := Set.image (fun value => naturalCode (code value)) Set.univ
  let subtypeSpace := Space.comap
    (fun value : {point : Real.UnitInterval // range point} => value.val)
    Real.unitBorel
  let forward : alpha → {point : Real.UnitInterval // range point} :=
    fun value => ⟨naturalCode (code value), value, True.intro, rfl⟩
  let inverse : {point : Real.UnitInterval // range point} → alpha :=
    fun point => Classical.choose point.property
  have inverseCode : ∀ point, naturalCode (code (inverse point)) = point.val := by
    intro point
    exact (Classical.choose_spec point.property).2
  have inverseForward : ∀ value, inverse (forward value) = value := by
    intro value
    exact injective (naturalCode_injective (inverseCode (forward value)))
  refine {
    range := range
    range_measurable := naturalCode_image_measurable code Set.univ
    equivalence := {
      forward := forward
      inverse := inverse
      inverse_forward := inverseForward
      forward_inverse := fun point => Subtype.ext (inverseCode point)
      forward_measurable := MeasurableMap.from_discrete subtypeSpace forward
      inverse_measurable := ?_
    }
  }
  intro set _
  have equal : Set.preimage inverse set =
      Set.preimage (fun value : {point : Real.UnitInterval // range point} =>
        value.val) (Set.image (fun value => naturalCode (code value)) set) := by
    apply Set.ext
    intro point
    constructor
    · intro member
      exact ⟨inverse point, member, inverseCode point⟩
    · rintro ⟨value, member, equal⟩
      have same : inverse point = value :=
        injective (naturalCode_injective ((inverseCode point).trans equal.symm))
      change set (inverse point)
      rw [same]
      exact member
  rw [equal]
  exact Space.comap_map _ Real.unitBorel (naturalCode_image_measurable code set)

/-- Standard Borel structure on the discrete natural numbers. -/
public noncomputable def natural : StandardBorel (Space.discrete Nat) :=
  ofNatInjection id (fun _ _ equal => equal)

/-- Standard Borel structure on the discrete unit space. -/
public noncomputable def unit : StandardBorel (Space.discrete Unit) :=
  ofNatInjection (fun _ => 0) (by
    intro left right _
    cases left
    cases right
    rfl)

/-- Standard Borel structure on an empty space without global inhabitant
assumptions. -/
@[expose] public noncomputable def ofEmpty {alpha : Type u} {space : Space alpha}
    (empty : ¬Nonempty alpha) : StandardBorel space := by
  have discrete : space = Space.discrete alpha := by
    apply Space.ext
    intro region
    constructor
    · intro _
      trivial
    · intro _
      have equal : region = Set.empty := by
        apply Set.ext
        intro point
        exact False.elim (empty ⟨point⟩)
      rw [equal]
      exact space.empty
  rw [discrete]
  exact ofNatInjection (fun _ => 0) (fun left _ _ => False.elim (empty ⟨left⟩))

end Problib.Measure.StandardBorel
