module

public import Problib.Measure.Additive.SFinite
public import Problib.Measure.Additive.Atom

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u
variable {α : Type u} (decode : Nat → Option α) (encode : α → Nat)
  (decode_encode : ∀ value, decode (encode value) = some value)
  (encode_decode : ∀ index value, decode index = some value → encode value = index)

/-- Counting on a countable discrete carrier. The two round trips ensure that
accepted indices cover the carrier without counting any value twice. Refused
indices contribute the zero measure, including on an empty carrier. -/
public noncomputable def countingOn (_ : ∀ value, decode (encode value) = some value)
    (_ : ∀ index value, decode index = some value → encode value = index) :
    Measure (Space.discrete α) :=
  Measure.sum fun index => match decode index with
    | none => Measure.zero _
    | some value => Measure.dirac _ value

/-- Every singleton has mass one, independently of its enumeration index. -/
public theorem countingOn_singleton (point : α) :
    countingOn decode encode decode_encode encode_decode (fun value => value = point) =
      ENNReal.one := by
  rw [countingOn, Measure.sum_apply _ True.intro]
  rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ (encode point)]
  · rw [decode_encode]
    exact Measure.dirac_apply_of_mem _ _ True.intro rfl
  · intro index different
    cases decoded : decode index with
    | none => exact Measure.zero_apply _
    | some value =>
        apply Measure.dirac_apply_of_not_mem _ _ True.intro
        intro equal
        subst value
        exact different (encode_decode index point decoded).symm

/-- Unit singleton masses characterize whole-carrier counting, so the
reference does not depend on which partial enumeration names its values. -/
public theorem countingOn_unique {measure : Measure (Space.discrete α)}
    (atoms : ∀ point, measure (fun value => value = point) = ENNReal.one) :
    countingOn decode encode decode_encode encode_decode = measure := by
  have injective : Function.Injective encode := by
    intro first second same
    have decoded := congrArg decode same
    rw [decode_encode, decode_encode] at decoded
    exact Option.some.inj decoded
  apply Measure.ext_of_atoms encode injective (fun _ => True.intro)
  intro point
  exact (countingOn_singleton _ _ _ _ point).trans (atoms point).symm

/-- A total enumeration has infinitely many accepted indices, each of mass
one, so its counting measure has infinite total mass. -/
public theorem countingOn_univ (total : ∀ index, (decode index).isSome = true) :
    countingOn decode encode decode_encode encode_decode Set.univ = ENNReal.top := by
  rw [countingOn, Measure.sum_apply _ True.intro]
  have one : ∀ index, (match decode index with
      | none => Measure.zero (Space.discrete α)
      | some value => Measure.dirac _ value) Set.univ = ENNReal.one := by
    intro index
    cases decoded : decode index with
    | none => have accepted := total index; simp [decoded] at accepted
    | some value => exact Measure.dirac_apply_univ _ _
  rw [ENNReal.tsum_congr one]
  exact ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero

/-- The singleton at each accepted index, or the empty set at a refused one,
is a finite cover of the counting measure. -/
public noncomputable def countingOnSigmaFinite :
    SigmaFinite (countingOn decode encode decode_encode encode_decode) :=
  SigmaFinite.ofCover {
    sets := fun index value => decode index = some value
    measurable := fun _ => True.intro
    finite := by
      intro index
      cases decoded : decode index with
      | none =>
          have empty : (fun value : α => (none : Option α) = some value) = Set.empty := by
            funext value
            simp [Set.empty]
          rw [empty, Measure.empty_apply]
          exact True.intro
      | some point =>
          have singleton : (fun value : α => some point = some value) =
              (fun value => value = point) := by
            funext value
            simp [eq_comm]
          rw [singleton, countingOn_singleton]
          exact True.intro
    cover := by
      apply Set.ext
      intro value
      exact ⟨fun _ => True.intro, fun _ => ⟨encode value, decode_encode value⟩⟩
  }

/-- The naturals specialize the general counting construction to the identity
enumeration. -/
public noncomputable def counting : Measure (Space.discrete Nat) :=
  countingOn some id (fun _ => rfl) (fun _ _ equal => (Option.some.inj equal).symm)

public theorem counting_singleton (point : Nat) :
    counting (fun value => value = point) = ENNReal.one :=
  countingOn_singleton _ _ _ _ point

public theorem counting_univ : counting Set.univ = ENNReal.top :=
  countingOn_univ _ _ _ _ (fun _ => rfl)

public noncomputable def countingSigmaFinite : SigmaFinite counting :=
  countingOnSigmaFinite _ _ _ _

end Problib.Measure.Measure
