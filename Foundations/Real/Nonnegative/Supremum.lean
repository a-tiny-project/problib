module

public import Foundations.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Foundations.Real

local notation "SignedReal" => Construction.Dedekind.selection.Carrier

namespace NNReal

private def liftedSet (set : NNReal → Prop) (value : SignedReal) : Prop :=
  ∃ candidate, set candidate ∧ toReal candidate = value

public theorem existsSup (set : NNReal → Prop)
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
  rcases Construction.Dedekind.existsLub (liftedSet set) liftedNonempty liftedBounded with
    ⟨least, leastUpper, leastLeast⟩
  have leastNonnegative : Construction.Dedekind.le Construction.Dedekind.zero least :=
    Construction.Dedekind.leTrans witness.property
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
  Classical.choose (existsSup set setNonempty setBounded)

public theorem supUpper (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    IsUpperBound le set (sup set setNonempty setBounded) :=
  (Classical.choose_spec (existsSup set setNonempty setBounded)).left

public theorem leSup {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {value : NNReal} (member : set value) :
    le value (sup set setNonempty setBounded) :=
  supUpper set setNonempty setBounded value member

public theorem supLeast {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {upper : NNReal} (upperBound : IsUpperBound le set upper) :
    le (sup set setNonempty setBounded) upper :=
  (Classical.choose_spec (existsSup set setNonempty setBounded)).right
    upper upperBound

public theorem supUnique {set : NNReal → Prop}
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper)
    {least : NNReal} (leastUpper : IsUpperBound le set least)
    (leastBelow : ∀ upper, IsUpperBound le set upper → le least upper) :
    sup set setNonempty setBounded = least :=
  leAntisymm
    (supLeast setNonempty setBounded leastUpper)
    (leastBelow _ (supUpper set setNonempty setBounded))

public theorem supMonotone {left right : NNReal → Prop}
    (leftNonempty : ∃ value, left value)
    (leftBounded : ∃ upper, IsUpperBound le left upper)
    (rightNonempty : ∃ value, right value)
    (rightBounded : ∃ upper, IsUpperBound le right upper)
    (included : ∀ value, left value → right value) :
    le (sup left leftNonempty leftBounded)
      (sup right rightNonempty rightBounded) :=
  supLeast leftNonempty leftBounded fun value member =>
    leSup rightNonempty rightBounded (included value member)

@[expose] public def addImage
    (factor : NNReal) (set : NNReal → Prop) (result : NNReal) : Prop :=
  ∃ value, set value ∧ result = add factor value

public theorem addImageNonempty (factor : NNReal) {set : NNReal → Prop}
    (setNonempty : ∃ value, set value) :
    ∃ result, addImage factor set result := by
  rcases setNonempty with ⟨value, member⟩
  exact ⟨add factor value, value, member, rfl⟩

public theorem addImageBounded (factor : NNReal) {set : NNReal → Prop}
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ upper, IsUpperBound le (addImage factor set) upper := by
  rcases setBounded with ⟨upper, upperBound⟩
  refine ⟨add factor upper, ?_⟩
  intro result member
  rcases member with ⟨value, valueMember, rfl⟩
  exact addLeAddLeft (upperBound value valueMember) factor

public theorem addSup (factor : NNReal) (set : NNReal → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    add factor (sup set setNonempty setBounded) =
      sup (addImage factor set)
        (addImageNonempty factor setNonempty)
        (addImageBounded factor setBounded) := by
  let imageSup := sup (addImage factor set)
    (addImageNonempty factor setNonempty)
    (addImageBounded factor setBounded)
  apply leAntisymm
  · rcases setNonempty with ⟨witness, witnessMember⟩
    have factorImage : le factor (add factor witness) := by
      simpa only [addZero] using addLeAddLeft (zeroLe witness) factor
    have imageTarget : le (add factor witness) imageSup :=
      leSup (addImageNonempty factor ⟨witness, witnessMember⟩)
        (addImageBounded factor setBounded)
        ⟨witness, witnessMember, rfl⟩
    have factorTarget : le factor imageSup :=
      leTrans factorImage imageTarget
    have differenceUpper : IsUpperBound le set (sub imageSup factor) := by
      intro value member
      apply (leSubIffAddLe factorTarget).mpr
      rw [addComm]
      exact leSup (addImageNonempty factor ⟨value, member⟩)
        (addImageBounded factor setBounded)
        ⟨value, member, rfl⟩
    have supremumDifference :
        le (sup set ⟨witness, witnessMember⟩ setBounded)
          (sub imageSup factor) :=
      supLeast ⟨witness, witnessMember⟩ setBounded differenceUpper
    have shifted := addLeAddLeft supremumDifference factor
    rw [addComm factor (sub imageSup factor),
      subAddCancel factorTarget] at shifted
    exact shifted
  · apply supLeast
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact addLeAddLeft
      (leSup setNonempty setBounded valueMember) factor

@[expose] public def mulImage
    (factor : NNReal) (set : NNReal → Prop) (result : NNReal) : Prop :=
  ∃ value, set value ∧ result = mul factor value

public theorem mulImageNonempty (factor : NNReal) {set : NNReal → Prop}
    (setNonempty : ∃ value, set value) :
    ∃ result, mulImage factor set result := by
  rcases setNonempty with ⟨value, member⟩
  exact ⟨mul factor value, value, member, rfl⟩

public theorem mulImageBounded (factor : NNReal) {set : NNReal → Prop}
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ upper, IsUpperBound le (mulImage factor set) upper := by
  rcases setBounded with ⟨upper, upperBound⟩
  refine ⟨mul factor upper, ?_⟩
  intro result member
  rcases member with ⟨value, valueMember, rfl⟩
  exact mulLeMulLeft (upperBound value valueMember) factor

public theorem mulSup (factor : NNReal) (factorPositive : lt zero factor)
    (set : NNReal → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    mul factor (sup set setNonempty setBounded) =
      sup (mulImage factor set)
        (mulImageNonempty factor setNonempty)
        (mulImageBounded factor setBounded) := by
  let imageSup := sup (mulImage factor set)
    (mulImageNonempty factor setNonempty)
    (mulImageBounded factor setBounded)
  have factorNonzero : factor ≠ zero :=
    (zeroLtIffNeZero factor).mp factorPositive
  apply leAntisymm
  · have quotientUpper : IsUpperBound le set (div imageSup factor) := by
      intro value member
      apply leOfMulLeMulLeft factorPositive
      rw [mulDivCancel imageSup factorNonzero]
      exact leSup (mulImageNonempty factor setNonempty)
        (mulImageBounded factor setBounded) ⟨value, member, rfl⟩
    have supremumQuotient :=
      supLeast setNonempty setBounded quotientUpper
    have scaled := mulLeMulLeft supremumQuotient factor
    rw [mulDivCancel imageSup factorNonzero] at scaled
    exact scaled
  · apply supLeast
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact mulLeMulLeft
      (leSup setNonempty setBounded valueMember) factor

end NNReal

end Foundations.Real
