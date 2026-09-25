module

public import Problib.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Problib.Real

local notation "SignedReal" => Construction.Dedekind.selection.Carrier

namespace NNReal

private def liftedSet (set : NNReal → Prop) (value : SignedReal) : Prop :=
  ∃ candidate, set candidate ∧ toReal candidate = value

public theorem exists_sup (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ least, IsLeastUpperBound le set least := by
  rcases setNonempty with ⟨witness, witnessMember⟩
  rcases setBounded with ⟨bound, boundUpper⟩
  have liftedNonempty : ∃ value, liftedSet set value :=
    ⟨toReal witness, witness, witnessMember, rfl⟩
  have liftedBounded :
      ∃ upper, IsUpperBound Construction.Dedekind.le (liftedSet set) upper := by
    refine ⟨toReal bound, ?_⟩
    intro value member
    rcases member with ⟨candidate, candidateMember, rfl⟩
    exact boundUpper candidate candidateMember
  rcases Construction.Dedekind.exists_lub (liftedSet set) liftedNonempty liftedBounded with
    ⟨least, leastUpper, leastLeast⟩
  have leastNonnegative : Construction.Dedekind.le Construction.Dedekind.zero least :=
    Construction.Dedekind.le_trans witness.property
      (leastUpper (toReal witness) ⟨witness, witnessMember, rfl⟩)
  let result : NNReal := ⟨least, leastNonnegative⟩
  refine ⟨result, ?_, ?_⟩
  · intro value member
    exact leastUpper (toReal value) ⟨value, member, rfl⟩
  · intro upper upperBound
    apply leastLeast (toReal upper)
    intro value member
    rcases member with ⟨candidate, candidateMember, rfl⟩
    exact upperBound candidate candidateMember

@[expose] public noncomputable def sup (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) : NNReal :=
  Classical.choose (exists_sup set setNonempty setBounded)

public theorem sup_upper (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    IsUpperBound le set (sup set setNonempty setBounded) :=
  (Classical.choose_spec (exists_sup set setNonempty setBounded)).left

public theorem le_sup {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {value : NNReal} (member : set value) :
    le value (sup set setNonempty setBounded) :=
  sup_upper set setNonempty setBounded value member

public theorem sup_least {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {upper : NNReal} (upperBound : IsUpperBound le set upper) :
    le (sup set setNonempty setBounded) upper :=
  (Classical.choose_spec (exists_sup set setNonempty setBounded)).right
    upper upperBound

public theorem sup_unique {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {least : NNReal} (leastUpper : IsUpperBound le set least)
    (leastBelow : ∀ upper, IsUpperBound le set upper → le least upper) :
    sup set setNonempty setBounded = least :=
  le_antisymm
    (sup_least setNonempty setBounded leastUpper)
    (leastBelow _ (sup_upper set setNonempty setBounded))

public theorem sup_monotone {left right : NNReal → Prop}
    (leftNonempty : ∃ value, left value)
    (leftBounded : ∃ upper, IsUpperBound le left upper)
    (rightNonempty : ∃ value, right value)
    (rightBounded : ∃ upper, IsUpperBound le right upper)
    (included : ∀ value, left value → right value) :
    le (sup left leftNonempty leftBounded)
      (sup right rightNonempty rightBounded) :=
  sup_least leftNonempty leftBounded fun value member =>
    le_sup rightNonempty rightBounded (included value member)

@[expose] public def addImage
    (factor : NNReal) (set : NNReal → Prop) (result : NNReal) : Prop :=
  ∃ value, set value ∧ result = add factor value

public theorem addImage_nonempty (factor : NNReal) {set : NNReal → Prop}
    (setNonempty : ∃ value, set value) :
    ∃ result, addImage factor set result := by
  rcases setNonempty with ⟨value, member⟩
  exact ⟨add factor value, value, member, rfl⟩

public theorem addImage_bounded (factor : NNReal) {set : NNReal → Prop}
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ upper, IsUpperBound le (addImage factor set) upper := by
  rcases setBounded with ⟨upper, upperBound⟩
  refine ⟨add factor upper, ?_⟩
  intro result member
  rcases member with ⟨value, valueMember, rfl⟩
  exact add_le_add_left (upperBound value valueMember) factor

public theorem add_sup (factor : NNReal) (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    add factor (sup set setNonempty setBounded) =
      sup (addImage factor set)
        (addImage_nonempty factor setNonempty)
        (addImage_bounded factor setBounded) := by
  let imageSup := sup (addImage factor set)
    (addImage_nonempty factor setNonempty)
    (addImage_bounded factor setBounded)
  apply le_antisymm
  · rcases setNonempty with ⟨witness, witnessMember⟩
    have factorImage : le factor (add factor witness) := by
      simpa only [add_zero] using add_le_add_left (zero_le witness) factor
    have imageTarget : le (add factor witness) imageSup :=
      le_sup (addImage_nonempty factor ⟨witness, witnessMember⟩)
        (addImage_bounded factor setBounded)
        ⟨witness, witnessMember, rfl⟩
    have factorTarget : le factor imageSup :=
      le_trans factorImage imageTarget
    have differenceUpper : IsUpperBound le set (sub imageSup factor) := by
      intro value member
      apply (le_sub_iff_add_le factorTarget).mpr
      rw [add_comm]
      exact le_sup (addImage_nonempty factor ⟨value, member⟩)
        (addImage_bounded factor setBounded)
        ⟨value, member, rfl⟩
    have supremumDifference :
        le (sup set ⟨witness, witnessMember⟩ setBounded)
          (sub imageSup factor) :=
      sup_least ⟨witness, witnessMember⟩ setBounded differenceUpper
    have shifted := add_le_add_left supremumDifference factor
    rw [add_comm factor (sub imageSup factor),
      sub_add_cancel factorTarget] at shifted
    exact shifted
  · apply sup_least
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact add_le_add_left
      (le_sup setNonempty setBounded valueMember) factor

@[expose] public def mulImage
    (factor : NNReal) (set : NNReal → Prop) (result : NNReal) : Prop :=
  ∃ value, set value ∧ result = mul factor value

public theorem mulImage_nonempty (factor : NNReal) {set : NNReal → Prop}
    (setNonempty : ∃ value, set value) :
    ∃ result, mulImage factor set result := by
  rcases setNonempty with ⟨value, member⟩
  exact ⟨mul factor value, value, member, rfl⟩

public theorem mulImage_bounded (factor : NNReal) {set : NNReal → Prop}
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ upper, IsUpperBound le (mulImage factor set) upper := by
  rcases setBounded with ⟨upper, upperBound⟩
  refine ⟨mul factor upper, ?_⟩
  intro result member
  rcases member with ⟨value, valueMember, rfl⟩
  exact mul_le_mul_left (upperBound value valueMember) factor

public theorem mul_sup (factor : NNReal) (factorPositive : lt zero factor)
    (set : NNReal → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    mul factor (sup set setNonempty setBounded) =
      sup (mulImage factor set)
        (mulImage_nonempty factor setNonempty)
        (mulImage_bounded factor setBounded) := by
  let imageSup := sup (mulImage factor set)
    (mulImage_nonempty factor setNonempty)
    (mulImage_bounded factor setBounded)
  have factorNonzero : factor ≠ zero :=
    (zero_lt_iff_ne_zero factor).mp factorPositive
  apply le_antisymm
  · have quotientUpper : IsUpperBound le set (div imageSup factor) := by
      intro value member
      apply le_of_mul_le_mul_left factorPositive
      rw [mul_div_cancel imageSup factorNonzero]
      exact le_sup (mulImage_nonempty factor setNonempty)
        (mulImage_bounded factor setBounded) ⟨value, member, rfl⟩
    have supremumQuotient :=
      sup_least setNonempty setBounded quotientUpper
    have scaled := mul_le_mul_left supremumQuotient factor
    rw [mul_div_cancel imageSup factorNonzero] at scaled
    exact scaled
  · apply sup_least
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact mul_le_mul_left
      (le_sup setNonempty setBounded valueMember) factor

end NNReal

end Problib.Real
