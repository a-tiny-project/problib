module

public import Foundations.Algebra.Order.Nonnegative

namespace Foundations.Algebra

public structure OrderedCommutativeRingLaws {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α) where
  multiplicative : MultiplicativeCommutativeMonoidLaws α
  one_nonnegative :
    base.order.le base.group.zero multiplicative.one
  mul_add : ∀ left middle right,
    multiplicative.mul left (base.group.add middle right) =
      base.group.add
        (multiplicative.mul left middle)
        (multiplicative.mul left right)
  product_nonnegative : ∀ {left right},
    base.order.le base.group.zero left →
    base.order.le base.group.zero right →
    base.order.le base.group.zero (multiplicative.mul left right)

namespace OrderedCommutativeRingLaws

public theorem mulZero {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base) (value : α) :
    laws.multiplicative.mul value base.group.zero = base.group.zero := by
  apply AdditiveCommutativeGroupLaws.addLeftCancel base.group
    (left := laws.multiplicative.mul value base.group.zero)
  calc
    base.group.add
        (laws.multiplicative.mul value base.group.zero)
        (laws.multiplicative.mul value base.group.zero) =
      laws.multiplicative.mul value
        (base.group.add base.group.zero base.group.zero) :=
      (laws.mul_add value base.group.zero base.group.zero).symm
    _ = laws.multiplicative.mul value base.group.zero := by
      rw [base.group.add_zero]
    _ = base.group.add
        (laws.multiplicative.mul value base.group.zero)
        base.group.zero :=
      (base.group.add_zero _).symm

public theorem zeroMul {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base) (value : α) :
    laws.multiplicative.mul base.group.zero value = base.group.zero := by
  rw [laws.multiplicative.mul_comm, laws.mulZero]

public theorem addMul {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base)
    (left middle right : α) :
    laws.multiplicative.mul (base.group.add left middle) right =
      base.group.add
        (laws.multiplicative.mul left right)
        (laws.multiplicative.mul middle right) := by
  rw [laws.multiplicative.mul_comm (base.group.add left middle) right,
    laws.mul_add,
    laws.multiplicative.mul_comm right left,
    laws.multiplicative.mul_comm right middle]

public theorem negMul {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base) (left right : α) :
    laws.multiplicative.mul (base.group.neg left) right =
      base.group.neg (laws.multiplicative.mul left right) := by
  apply AdditiveCommutativeGroupLaws.addLeftCancel base.group
    (left := laws.multiplicative.mul left right)
  calc
    base.group.add
        (laws.multiplicative.mul left right)
        (laws.multiplicative.mul (base.group.neg left) right) =
      laws.multiplicative.mul
        (base.group.add left (base.group.neg left)) right :=
      (laws.addMul left (base.group.neg left) right).symm
    _ = laws.multiplicative.mul base.group.zero right := by
      rw [base.group.add_neg]
    _ = base.group.zero := laws.zeroMul right
    _ = base.group.add
        (laws.multiplicative.mul left right)
        (base.group.neg (laws.multiplicative.mul left right)) :=
      (base.group.add_neg _).symm

public theorem mulNeg {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base) (left right : α) :
    laws.multiplicative.mul left (base.group.neg right) =
      base.group.neg (laws.multiplicative.mul left right) := by
  rw [laws.multiplicative.mul_comm left (base.group.neg right),
    laws.negMul,
    laws.multiplicative.mul_comm right left]

public theorem negMulNeg {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base) (left right : α) :
    laws.multiplicative.mul
        (base.group.neg left) (base.group.neg right) =
      laws.multiplicative.mul left right := by
  rw [laws.negMul, laws.mulNeg,
    AdditiveCommutativeGroupLaws.negNeg base.group]

public theorem mulLeMulNonnegativeRight {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base)
    {left right factor : α} (included : base.order.le left right)
    (factorNonnegative : base.order.le base.group.zero factor) :
    base.order.le
      (laws.multiplicative.mul left factor)
      (laws.multiplicative.mul right factor) := by
  have differenceNonnegative :=
    base.toOrderedAdditiveCommutativeGroupLaws.subNonnegativeOfLe included
  have productNonnegative := laws.product_nonnegative
    differenceNonnegative factorNonnegative
  apply base.toOrderedAdditiveCommutativeGroupLaws.leOfSubNonnegative
  simpa only [AdditiveCommutativeGroupLaws.sub, laws.addMul,
    laws.negMul] using productNonnegative

public theorem mulLeMulNonnegativeLeft {α : Type}
    {base : LinearlyOrderedAdditiveCommutativeGroupLaws α}
    (laws : OrderedCommutativeRingLaws base)
    {left right factor : α} (included : base.order.le left right)
    (factorNonnegative : base.order.le base.group.zero factor) :
    base.order.le
      (laws.multiplicative.mul factor left)
      (laws.multiplicative.mul factor right) := by
  rw [laws.multiplicative.mul_comm factor left,
    laws.multiplicative.mul_comm factor right]
  exact laws.mulLeMulNonnegativeRight included factorNonnegative

end OrderedCommutativeRingLaws

namespace NonnegativeMultiplicationKernel

@[expose] public noncomputable def signedMul {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) : α := by
  classical
  exact
    if leftNonnegative : base.order.le base.group.zero left then
      if rightNonnegative : base.order.le base.group.zero right then
        (kernel.mul ⟨left, leftNonnegative⟩
          ⟨right, rightNonnegative⟩).val
      else
        base.group.neg
          (kernel.mul ⟨left, leftNonnegative⟩
            ⟨base.group.neg right,
              base.negNonnegativeOfNotNonnegative rightNonnegative⟩).val
    else
      if rightNonnegative : base.order.le base.group.zero right then
        base.group.neg
          (kernel.mul
            ⟨base.group.neg left,
              base.negNonnegativeOfNotNonnegative leftNonnegative⟩
            ⟨right, rightNonnegative⟩).val
      else
        (kernel.mul
          ⟨base.group.neg left,
            base.negNonnegativeOfNotNonnegative leftNonnegative⟩
          ⟨base.group.neg right,
            base.negNonnegativeOfNotNonnegative rightNonnegative⟩).val

public theorem signedMulOfNonnegativeOfNonnegative {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    {left right : α}
    (leftNonnegative : base.order.le base.group.zero left)
    (rightNonnegative : base.order.le base.group.zero right) :
    signedMul base kernel left right =
      (kernel.mul ⟨left, leftNonnegative⟩
        ⟨right, rightNonnegative⟩).val := by
  classical
  unfold signedMul
  simp only [dif_pos leftNonnegative, dif_pos rightNonnegative]

public theorem signedMulOfNonnegativeOfNotNonnegative {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    {left right : α}
    (leftNonnegative : base.order.le base.group.zero left)
    (rightNotNonnegative : ¬base.order.le base.group.zero right) :
    signedMul base kernel left right =
      base.group.neg
        (kernel.mul ⟨left, leftNonnegative⟩
          ⟨base.group.neg right,
            base.negNonnegativeOfNotNonnegative
              rightNotNonnegative⟩).val := by
  classical
  unfold signedMul
  simp only [dif_pos leftNonnegative, dif_neg rightNotNonnegative]

public theorem signedMulOfNotNonnegativeOfNonnegative {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    {left right : α}
    (leftNotNonnegative : ¬base.order.le base.group.zero left)
    (rightNonnegative : base.order.le base.group.zero right) :
    signedMul base kernel left right =
      base.group.neg
        (kernel.mul
          ⟨base.group.neg left,
            base.negNonnegativeOfNotNonnegative leftNotNonnegative⟩
          ⟨right, rightNonnegative⟩).val := by
  classical
  unfold signedMul
  simp only [dif_neg leftNotNonnegative, dif_pos rightNonnegative]

public theorem signedMulOfNotNonnegativeOfNotNonnegative {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    {left right : α}
    (leftNotNonnegative : ¬base.order.le base.group.zero left)
    (rightNotNonnegative : ¬base.order.le base.group.zero right) :
    signedMul base kernel left right =
      (kernel.mul
        ⟨base.group.neg left,
          base.negNonnegativeOfNotNonnegative leftNotNonnegative⟩
        ⟨base.group.neg right,
          base.negNonnegativeOfNotNonnegative rightNotNonnegative⟩).val := by
  classical
  unfold signedMul
  simp only [dif_neg leftNotNonnegative, dif_neg rightNotNonnegative]

private theorem signedMulZero {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws) (value : α) :
    signedMul base kernel value base.group.zero = base.group.zero := by
  let valueCone (nonnegative : base.order.le base.group.zero value) :
      NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨value, nonnegative⟩
  by_cases valueNonnegative : base.order.le base.group.zero value
  · rw [signedMulOfNonnegativeOfNonnegative base kernel
      valueNonnegative (base.order.refl base.group.zero)]
    have vanished := congrArg Subtype.val
      (kernel.mulZero (valueCone valueNonnegative))
    simpa only [valueCone, NonnegativePart.zero] using vanished
  · rw [signedMulOfNotNonnegativeOfNonnegative base kernel
      valueNonnegative (base.order.refl base.group.zero)]
    let negatedCone :
        NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
      ⟨base.group.neg value,
        base.negNonnegativeOfNotNonnegative valueNonnegative⟩
    have vanished := congrArg Subtype.val (kernel.mulZero negatedCone)
    calc
      base.group.neg
          (kernel.mul
            ⟨base.group.neg value,
              base.negNonnegativeOfNotNonnegative valueNonnegative⟩
            ⟨base.group.zero, base.order.refl base.group.zero⟩).val =
        base.group.neg base.group.zero := by
          apply congrArg base.group.neg
          simpa only [negatedCone, NonnegativePart.zero] using vanished
      _ = base.group.zero :=
        AdditiveCommutativeGroupLaws.negZero base.group

private theorem signedZeroMul {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws) (value : α) :
    signedMul base kernel base.group.zero value = base.group.zero := by
  let valueCone (nonnegative : base.order.le base.group.zero value) :
      NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨value, nonnegative⟩
  by_cases valueNonnegative : base.order.le base.group.zero value
  · rw [signedMulOfNonnegativeOfNonnegative base kernel
      (base.order.refl base.group.zero) valueNonnegative]
    have vanished := congrArg Subtype.val
      (kernel.zeroMul (valueCone valueNonnegative))
    simpa only [valueCone, NonnegativePart.zero] using vanished
  · rw [signedMulOfNonnegativeOfNotNonnegative base kernel
      (base.order.refl base.group.zero) valueNonnegative]
    let negatedCone :
        NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
      ⟨base.group.neg value,
        base.negNonnegativeOfNotNonnegative valueNonnegative⟩
    have vanished := congrArg Subtype.val (kernel.zeroMul negatedCone)
    calc
      base.group.neg
          (kernel.mul
            ⟨base.group.zero, base.order.refl base.group.zero⟩
            ⟨base.group.neg value,
              base.negNonnegativeOfNotNonnegative valueNonnegative⟩).val =
        base.group.neg base.group.zero := by
          apply congrArg base.group.neg
          simpa only [negatedCone, NonnegativePart.zero] using vanished
      _ = base.group.zero :=
        AdditiveCommutativeGroupLaws.negZero base.group

private theorem signedMulComm {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) :
    signedMul base kernel left right = signedMul base kernel right left := by
  by_cases leftNonnegative : base.order.le base.group.zero left
  · by_cases rightNonnegative : base.order.le base.group.zero right
    · rw [signedMulOfNonnegativeOfNonnegative base kernel
          leftNonnegative rightNonnegative,
        signedMulOfNonnegativeOfNonnegative base kernel
          rightNonnegative leftNonnegative]
      exact congrArg Subtype.val
        (kernel.mul_comm ⟨left, leftNonnegative⟩
          ⟨right, rightNonnegative⟩)
    · rw [signedMulOfNonnegativeOfNotNonnegative base kernel
          leftNonnegative rightNonnegative,
        signedMulOfNotNonnegativeOfNonnegative base kernel
          rightNonnegative leftNonnegative]
      exact congrArg base.group.neg (congrArg Subtype.val
        (kernel.mul_comm ⟨left, leftNonnegative⟩
          ⟨base.group.neg right,
            base.negNonnegativeOfNotNonnegative rightNonnegative⟩))
  · by_cases rightNonnegative : base.order.le base.group.zero right
    · rw [signedMulOfNotNonnegativeOfNonnegative base kernel
          leftNonnegative rightNonnegative,
        signedMulOfNonnegativeOfNotNonnegative base kernel
          rightNonnegative leftNonnegative]
      exact congrArg base.group.neg (congrArg Subtype.val
        (kernel.mul_comm
          ⟨base.group.neg left,
            base.negNonnegativeOfNotNonnegative leftNonnegative⟩
          ⟨right, rightNonnegative⟩))
    · rw [signedMulOfNotNonnegativeOfNotNonnegative base kernel
          leftNonnegative rightNonnegative,
        signedMulOfNotNonnegativeOfNotNonnegative base kernel
          rightNonnegative leftNonnegative]
      exact congrArg Subtype.val
        (kernel.mul_comm
          ⟨base.group.neg left,
            base.negNonnegativeOfNotNonnegative leftNonnegative⟩
          ⟨base.group.neg right,
            base.negNonnegativeOfNotNonnegative rightNonnegative⟩)

private theorem signedMulOne {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws) (value : α) :
    signedMul base kernel value kernel.one.val = value := by
  let valueCone (nonnegative : base.order.le base.group.zero value) :
      NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨value, nonnegative⟩
  by_cases valueNonnegative : base.order.le base.group.zero value
  · rw [signedMulOfNonnegativeOfNonnegative base kernel
      valueNonnegative kernel.one.property]
    let oneCone :
        NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
      ⟨kernel.one.val, kernel.one.property⟩
    have oneEqual : oneCone = kernel.one := by
      apply NonnegativePart.ext
      rfl
    have aligned := congrArg Subtype.val
      (congrArg (fun cone => kernel.mul (valueCone valueNonnegative) cone)
        oneEqual)
    have identity := congrArg Subtype.val
      (kernel.mul_one (valueCone valueNonnegative))
    exact (by
      simpa only [valueCone, oneCone] using aligned.trans identity)
  · rw [signedMulOfNotNonnegativeOfNonnegative base kernel
      valueNonnegative kernel.one.property]
    let negatedCone :
        NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
      ⟨base.group.neg value,
        base.negNonnegativeOfNotNonnegative valueNonnegative⟩
    let oneCone :
        NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
      ⟨kernel.one.val, kernel.one.property⟩
    have oneEqual : oneCone = kernel.one := by
      apply NonnegativePart.ext
      rfl
    have aligned := congrArg Subtype.val
      (congrArg (fun cone => kernel.mul negatedCone cone) oneEqual)
    have identity := congrArg Subtype.val (kernel.mul_one negatedCone)
    calc
      base.group.neg
          (kernel.mul
            ⟨base.group.neg value,
              base.negNonnegativeOfNotNonnegative valueNonnegative⟩
            ⟨kernel.one.val, kernel.one.property⟩).val =
        base.group.neg (base.group.neg value) := by
          apply congrArg base.group.neg
          simpa only [negatedCone, oneCone] using aligned.trans identity
      _ = value := AdditiveCommutativeGroupLaws.negNeg base.group value

private theorem signedNegMul {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) :
    signedMul base kernel (base.group.neg left) right =
      base.group.neg (signedMul base kernel left right) := by
  by_cases leftNonnegative : base.order.le base.group.zero left
  · by_cases negLeftNonnegative :
        base.order.le base.group.zero (base.group.neg left)
    · have leftZero :=
        base.eqZeroOfNonnegativeOfNegNonnegative
          leftNonnegative negLeftNonnegative
      subst left
      simp only [AdditiveCommutativeGroupLaws.negZero,
        signedZeroMul]
    · by_cases rightNonnegative : base.order.le base.group.zero right
      · let restoredCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨base.group.neg (base.group.neg left),
            base.negNonnegativeOfNotNonnegative negLeftNonnegative⟩
        let leftCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨left, leftNonnegative⟩
        let rightCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨right, rightNonnegative⟩
        have restoredEqual : restoredCone = leftCone := by
          apply NonnegativePart.ext
          exact AdditiveCommutativeGroupLaws.negNeg base.group left
        have productsEqual :
            (kernel.mul restoredCone rightCone).val =
              (kernel.mul leftCone rightCone).val :=
          congrArg Subtype.val
            (congrArg (fun cone => kernel.mul cone rightCone) restoredEqual)
        calc
          signedMul base kernel (base.group.neg left) right =
              base.group.neg (kernel.mul restoredCone rightCone).val := by
            simpa only [restoredCone, rightCone] using
              signedMulOfNotNonnegativeOfNonnegative base kernel
                negLeftNonnegative rightNonnegative
          _ = base.group.neg (kernel.mul leftCone rightCone).val :=
            congrArg base.group.neg productsEqual
          _ = base.group.neg (signedMul base kernel left right) := by
            rw [signedMulOfNonnegativeOfNonnegative base kernel
              leftNonnegative rightNonnegative]
      · let restoredCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨base.group.neg (base.group.neg left),
            base.negNonnegativeOfNotNonnegative negLeftNonnegative⟩
        let leftCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨left, leftNonnegative⟩
        let negRightCone :
            NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
          ⟨base.group.neg right,
            base.negNonnegativeOfNotNonnegative rightNonnegative⟩
        have restoredEqual : restoredCone = leftCone := by
          apply NonnegativePart.ext
          exact AdditiveCommutativeGroupLaws.negNeg base.group left
        have productsEqual :
            (kernel.mul restoredCone negRightCone).val =
              (kernel.mul leftCone negRightCone).val :=
          congrArg Subtype.val
            (congrArg (fun cone => kernel.mul cone negRightCone)
              restoredEqual)
        calc
          signedMul base kernel (base.group.neg left) right =
              (kernel.mul restoredCone negRightCone).val := by
            simpa only [restoredCone, negRightCone] using
              signedMulOfNotNonnegativeOfNotNonnegative base kernel
                negLeftNonnegative rightNonnegative
          _ = (kernel.mul leftCone negRightCone).val := productsEqual
          _ = base.group.neg
              (base.group.neg (kernel.mul leftCone negRightCone).val) :=
            (AdditiveCommutativeGroupLaws.negNeg base.group _).symm
          _ = base.group.neg (signedMul base kernel left right) := by
            rw [signedMulOfNonnegativeOfNotNonnegative base kernel
              leftNonnegative rightNonnegative]
  · have negLeftNonnegative :=
      base.negNonnegativeOfNotNonnegative leftNonnegative
    by_cases rightNonnegative : base.order.le base.group.zero right
    · let negLeftCone :
          NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
        ⟨base.group.neg left, negLeftNonnegative⟩
      let rightCone :
          NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
        ⟨right, rightNonnegative⟩
      calc
        signedMul base kernel (base.group.neg left) right =
            (kernel.mul negLeftCone rightCone).val := by
          simpa only [negLeftCone, rightCone] using
            signedMulOfNonnegativeOfNonnegative base kernel
              negLeftNonnegative rightNonnegative
        _ = base.group.neg
            (base.group.neg (kernel.mul negLeftCone rightCone).val) :=
          (AdditiveCommutativeGroupLaws.negNeg base.group _).symm
        _ = base.group.neg (signedMul base kernel left right) := by
          rw [signedMulOfNotNonnegativeOfNonnegative base kernel
            leftNonnegative rightNonnegative]
    · let negLeftCone :
          NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
        ⟨base.group.neg left, negLeftNonnegative⟩
      let negRightCone :
          NonnegativePart base.toOrderedAdditiveCommutativeGroupLaws :=
        ⟨base.group.neg right,
          base.negNonnegativeOfNotNonnegative rightNonnegative⟩
      calc
        signedMul base kernel (base.group.neg left) right =
            base.group.neg (kernel.mul negLeftCone negRightCone).val := by
          simpa only [negLeftCone, negRightCone] using
            signedMulOfNonnegativeOfNotNonnegative base kernel
              negLeftNonnegative rightNonnegative
        _ = base.group.neg (signedMul base kernel left right) := by
          rw [signedMulOfNotNonnegativeOfNotNonnegative base kernel
            leftNonnegative rightNonnegative]

private theorem signedMulNeg {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) :
    signedMul base kernel left (base.group.neg right) =
      base.group.neg (signedMul base kernel left right) := by
  rw [signedMulComm base kernel left (base.group.neg right),
    signedNegMul base kernel right left,
    signedMulComm base kernel right left]

private theorem signedNegMulNeg {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) :
    signedMul base kernel (base.group.neg left) (base.group.neg right) =
      signedMul base kernel left right := by
  rw [signedNegMul base kernel left (base.group.neg right),
    signedMulNeg base kernel left right,
    AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAssocNonnegativeAll {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left middle right : α)
    (leftNonnegative : base.order.le base.group.zero left)
    (middleNonnegative : base.order.le base.group.zero middle)
    (rightNonnegative : base.order.le base.group.zero right) :
    signedMul base kernel (signedMul base kernel left middle) right =
      signedMul base kernel left (signedMul base kernel middle right) := by
  let leftCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨left, leftNonnegative⟩
  let middleCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨middle, middleNonnegative⟩
  let rightCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨right, rightNonnegative⟩
  have leftMiddleNonnegative := (kernel.mul leftCone middleCone).property
  have middleRightNonnegative := (kernel.mul middleCone rightCone).property
  rw [signedMulOfNonnegativeOfNonnegative base kernel
      leftNonnegative middleNonnegative,
    signedMulOfNonnegativeOfNonnegative base kernel
      leftMiddleNonnegative rightNonnegative,
    signedMulOfNonnegativeOfNonnegative base kernel
      middleNonnegative rightNonnegative,
    signedMulOfNonnegativeOfNonnegative base kernel
      leftNonnegative middleRightNonnegative]
  exact congrArg Subtype.val
    (kernel.mul_assoc leftCone middleCone rightCone)

private theorem signedMulAssocNonnegativeLeftTwo {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left middle right : α)
    (leftNonnegative : base.order.le base.group.zero left)
    (middleNonnegative : base.order.le base.group.zero middle) :
    signedMul base kernel (signedMul base kernel left middle) right =
      signedMul base kernel left (signedMul base kernel middle right) := by
  by_cases rightNonnegative : base.order.le base.group.zero right
  · exact signedMulAssocNonnegativeAll base kernel left middle right
      leftNonnegative middleNonnegative rightNonnegative
  · have negRightNonnegative :=
      base.negNonnegativeOfNotNonnegative rightNonnegative
    have baseAssoc := signedMulAssocNonnegativeAll base kernel
      left middle (base.group.neg right)
      leftNonnegative middleNonnegative negRightNonnegative
    calc
      signedMul base kernel (signedMul base kernel left middle) right =
          signedMul base kernel (signedMul base kernel left middle)
            (base.group.neg (base.group.neg right)) := by
              rw [AdditiveCommutativeGroupLaws.negNeg base.group]
      _ = base.group.neg
          (signedMul base kernel (signedMul base kernel left middle)
            (base.group.neg right)) :=
        signedMulNeg base kernel _ _
      _ = base.group.neg
          (signedMul base kernel left
            (signedMul base kernel middle (base.group.neg right))) := by
        rw [baseAssoc]
      _ = signedMul base kernel left
          (base.group.neg
            (signedMul base kernel middle (base.group.neg right))) := by
        rw [← signedMulNeg base kernel]
      _ = signedMul base kernel left
          (signedMul base kernel middle
            (base.group.neg (base.group.neg right))) := by
        rw [← signedMulNeg base kernel]
      _ = signedMul base kernel left
          (signedMul base kernel middle right) := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAssocNonnegativeLeft {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left middle right : α)
    (leftNonnegative : base.order.le base.group.zero left) :
    signedMul base kernel (signedMul base kernel left middle) right =
      signedMul base kernel left (signedMul base kernel middle right) := by
  by_cases middleNonnegative : base.order.le base.group.zero middle
  · exact signedMulAssocNonnegativeLeftTwo base kernel left middle right
      leftNonnegative middleNonnegative
  · have negMiddleNonnegative :=
      base.negNonnegativeOfNotNonnegative middleNonnegative
    have baseAssoc := signedMulAssocNonnegativeLeftTwo base kernel
      left (base.group.neg middle) right
      leftNonnegative negMiddleNonnegative
    calc
      signedMul base kernel (signedMul base kernel left middle) right =
          signedMul base kernel
            (signedMul base kernel left
              (base.group.neg (base.group.neg middle))) right := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]
      _ = signedMul base kernel
          (base.group.neg
            (signedMul base kernel left (base.group.neg middle))) right := by
        rw [signedMulNeg base kernel]
      _ = base.group.neg
          (signedMul base kernel
            (signedMul base kernel left (base.group.neg middle)) right) := by
        rw [signedNegMul base kernel]
      _ = base.group.neg
          (signedMul base kernel left
            (signedMul base kernel (base.group.neg middle) right)) := by
        rw [baseAssoc]
      _ = signedMul base kernel left
          (base.group.neg
            (signedMul base kernel (base.group.neg middle) right)) := by
        rw [← signedMulNeg base kernel]
      _ = signedMul base kernel left
          (signedMul base kernel
            (base.group.neg (base.group.neg middle)) right) := by
        rw [← signedNegMul base kernel]
      _ = signedMul base kernel left
          (signedMul base kernel middle right) := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAssoc {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left middle right : α) :
    signedMul base kernel (signedMul base kernel left middle) right =
      signedMul base kernel left (signedMul base kernel middle right) := by
  by_cases leftNonnegative : base.order.le base.group.zero left
  · exact signedMulAssocNonnegativeLeft base kernel left middle right
      leftNonnegative
  · have negLeftNonnegative :=
      base.negNonnegativeOfNotNonnegative leftNonnegative
    have baseAssoc := signedMulAssocNonnegativeLeft base kernel
      (base.group.neg left) middle right negLeftNonnegative
    calc
      signedMul base kernel (signedMul base kernel left middle) right =
          signedMul base kernel
            (signedMul base kernel
              (base.group.neg (base.group.neg left)) middle) right := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]
      _ = signedMul base kernel
          (base.group.neg
            (signedMul base kernel (base.group.neg left) middle)) right := by
        rw [signedNegMul base kernel]
      _ = base.group.neg
          (signedMul base kernel
            (signedMul base kernel (base.group.neg left) middle) right) := by
        rw [signedNegMul base kernel]
      _ = base.group.neg
          (signedMul base kernel (base.group.neg left)
            (signedMul base kernel middle right)) := by
        rw [baseAssoc]
      _ = signedMul base kernel
          (base.group.neg (base.group.neg left))
          (signedMul base kernel middle right) := by
        rw [← signedNegMul base kernel]
      _ = signedMul base kernel left
          (signedMul base kernel middle right) := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAddNonnegativeAll {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (factor left right : α)
    (factorNonnegative : base.order.le base.group.zero factor)
    (leftNonnegative : base.order.le base.group.zero left)
    (rightNonnegative : base.order.le base.group.zero right) :
    signedMul base kernel factor (base.group.add left right) =
      base.group.add (signedMul base kernel factor left)
        (signedMul base kernel factor right) := by
  let factorCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨factor, factorNonnegative⟩
  let leftCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨left, leftNonnegative⟩
  let rightCone : NonnegativePart
      base.toOrderedAdditiveCommutativeGroupLaws :=
    ⟨right, rightNonnegative⟩
  have sumNonnegative :
      base.order.le base.group.zero (base.group.add left right) :=
    (NonnegativePart.add leftCone rightCone).property
  rw [signedMulOfNonnegativeOfNonnegative base kernel
      factorNonnegative sumNonnegative,
    signedMulOfNonnegativeOfNonnegative base kernel
      factorNonnegative leftNonnegative,
    signedMulOfNonnegativeOfNonnegative base kernel
      factorNonnegative rightNonnegative]
  have distributed := congrArg Subtype.val
    (kernel.mul_add factorCone leftCone rightCone)
  simpa only [factorCone, leftCone, rightCone,
    NonnegativePart.add] using distributed

private theorem signedMulAddNonnegativePositiveNegative {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (factor left right : α)
    (factorNonnegative : base.order.le base.group.zero factor)
    (leftNonnegative : base.order.le base.group.zero left)
    (rightNotNonnegative : ¬base.order.le base.group.zero right) :
    signedMul base kernel factor (base.group.add left right) =
      base.group.add (signedMul base kernel factor left)
        (signedMul base kernel factor right) := by
  have negRightNonnegative :=
    base.negNonnegativeOfNotNonnegative rightNotNonnegative
  by_cases sumNonnegative :
      base.order.le base.group.zero (base.group.add left right)
  · have sumCancel :
        base.group.add (base.group.add left right)
          (base.group.neg right) = left := by
      rw [base.group.add_assoc, base.group.add_neg,
        base.group.add_zero]
    have distributed := signedMulAddNonnegativeAll base kernel factor
      (base.group.add left right) (base.group.neg right)
      factorNonnegative sumNonnegative negRightNonnegative
    rw [sumCancel] at distributed
    have isolated := AdditiveCommutativeGroupLaws.addNegEqOfEqAdd
      base.group distributed
    calc
      signedMul base kernel factor (base.group.add left right) =
          base.group.add (signedMul base kernel factor left)
            (base.group.neg
              (signedMul base kernel factor (base.group.neg right))) :=
        isolated
      _ = base.group.add (signedMul base kernel factor left)
          (signedMul base kernel factor right) := by
        rw [← signedMulNeg base kernel,
          AdditiveCommutativeGroupLaws.negNeg base.group]
  · have negSumNonnegative :=
      base.negNonnegativeOfNotNonnegative sumNonnegative
    have negSumAddLeft :
        base.group.add
          (base.group.neg (base.group.add left right)) left =
          base.group.neg right :=
      AdditiveCommutativeGroupLaws.negAddAddLeft base.group left right
    have distributed := signedMulAddNonnegativeAll base kernel factor
      (base.group.neg (base.group.add left right)) left
      factorNonnegative negSumNonnegative leftNonnegative
    rw [negSumAddLeft] at distributed
    rw [signedMulNeg base kernel factor
      (base.group.add left right)] at distributed
    have shifted := AdditiveCommutativeGroupLaws.eqAddOfEqNegAdd
      base.group distributed
    have isolated := AdditiveCommutativeGroupLaws.addNegEqOfEqAdd
      base.group shifted
    calc
      signedMul base kernel factor (base.group.add left right) =
          base.group.add (signedMul base kernel factor left)
            (base.group.neg
              (signedMul base kernel factor (base.group.neg right))) :=
        isolated
      _ = base.group.add (signedMul base kernel factor left)
          (signedMul base kernel factor right) := by
        rw [← signedMulNeg base kernel,
          AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAddNonnegativeFactor {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (factor left right : α)
    (factorNonnegative : base.order.le base.group.zero factor) :
    signedMul base kernel factor (base.group.add left right) =
      base.group.add (signedMul base kernel factor left)
        (signedMul base kernel factor right) := by
  by_cases leftNonnegative : base.order.le base.group.zero left
  · by_cases rightNonnegative : base.order.le base.group.zero right
    · exact signedMulAddNonnegativeAll base kernel factor left right
        factorNonnegative leftNonnegative rightNonnegative
    · exact signedMulAddNonnegativePositiveNegative base kernel
        factor left right factorNonnegative leftNonnegative rightNonnegative
  · by_cases rightNonnegative : base.order.le base.group.zero right
    · have swapped := signedMulAddNonnegativePositiveNegative base kernel
        factor right left factorNonnegative rightNonnegative leftNonnegative
      rw [base.group.add_comm left right,
        base.group.add_comm
          (signedMul base kernel factor left)
          (signedMul base kernel factor right)]
      exact swapped
    · have negLeftNonnegative :=
        base.negNonnegativeOfNotNonnegative leftNonnegative
      have negRightNonnegative :=
        base.negNonnegativeOfNotNonnegative rightNonnegative
      have distributed := signedMulAddNonnegativeAll base kernel factor
        (base.group.neg left) (base.group.neg right)
        factorNonnegative negLeftNonnegative negRightNonnegative
      calc
        signedMul base kernel factor (base.group.add left right) =
            signedMul base kernel factor
              (base.group.neg
                (base.group.neg (base.group.add left right))) := by
          rw [AdditiveCommutativeGroupLaws.negNeg base.group]
        _ = base.group.neg
            (signedMul base kernel factor
              (base.group.neg (base.group.add left right))) :=
          signedMulNeg base kernel _ _
        _ = base.group.neg
            (signedMul base kernel factor
              (base.group.add (base.group.neg left)
                (base.group.neg right))) := by
          rw [AdditiveCommutativeGroupLaws.negAddDistrib base.group]
        _ = base.group.neg
            (base.group.add
              (signedMul base kernel factor (base.group.neg left))
              (signedMul base kernel factor (base.group.neg right))) := by
          rw [distributed]
        _ = base.group.add
            (base.group.neg
              (signedMul base kernel factor (base.group.neg left)))
            (base.group.neg
              (signedMul base kernel factor (base.group.neg right))) :=
          AdditiveCommutativeGroupLaws.negAddDistrib base.group _ _
        _ = base.group.add (signedMul base kernel factor left)
            (signedMul base kernel factor right) := by
          rw [← signedMulNeg base kernel,
            AdditiveCommutativeGroupLaws.negNeg base.group,
            ← signedMulNeg base kernel,
            AdditiveCommutativeGroupLaws.negNeg base.group]

private theorem signedMulAdd {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (factor left right : α) :
    signedMul base kernel factor (base.group.add left right) =
      base.group.add (signedMul base kernel factor left)
        (signedMul base kernel factor right) := by
  by_cases factorNonnegative : base.order.le base.group.zero factor
  · exact signedMulAddNonnegativeFactor base kernel factor left right
      factorNonnegative
  · have negFactorNonnegative :=
      base.negNonnegativeOfNotNonnegative factorNonnegative
    have distributed := signedMulAddNonnegativeFactor base kernel
      (base.group.neg factor) left right negFactorNonnegative
    calc
      signedMul base kernel factor (base.group.add left right) =
          signedMul base kernel
            (base.group.neg (base.group.neg factor))
            (base.group.add left right) := by
        rw [AdditiveCommutativeGroupLaws.negNeg base.group]
      _ = base.group.neg
          (signedMul base kernel (base.group.neg factor)
            (base.group.add left right)) :=
        signedNegMul base kernel _ _
      _ = base.group.neg
          (base.group.add
            (signedMul base kernel (base.group.neg factor) left)
            (signedMul base kernel (base.group.neg factor) right)) := by
        rw [distributed]
      _ = base.group.add
          (base.group.neg
            (signedMul base kernel (base.group.neg factor) left))
          (base.group.neg
            (signedMul base kernel (base.group.neg factor) right)) :=
        AdditiveCommutativeGroupLaws.negAddDistrib base.group _ _
      _ = base.group.add (signedMul base kernel factor left)
          (signedMul base kernel factor right) := by
        rw [← signedNegMul base kernel,
          AdditiveCommutativeGroupLaws.negNeg base.group,
          ← signedNegMul base kernel,
          AdditiveCommutativeGroupLaws.negNeg base.group]

public noncomputable def extend {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws) :
    OrderedCommutativeRingLaws base where
  multiplicative := {
    one := kernel.one.val
    mul := signedMul base kernel
    mul_comm := signedMulComm base kernel
    mul_assoc := signedMulAssoc base kernel
    mul_one := signedMulOne base kernel
  }
  one_nonnegative := kernel.one.property
  mul_add := signedMulAdd base kernel
  product_nonnegative := by
    intro left right leftNonnegative rightNonnegative
    change base.order.le base.group.zero
      (signedMul base kernel left right)
    rw [signedMulOfNonnegativeOfNonnegative base kernel
      leftNonnegative rightNonnegative]
    exact (kernel.mul ⟨left, leftNonnegative⟩
      ⟨right, rightNonnegative⟩).property

theorem extendMul {α : Type}
    (base : LinearlyOrderedAdditiveCommutativeGroupLaws α)
    (kernel : NonnegativeMultiplicationKernel
      base.toOrderedAdditiveCommutativeGroupLaws)
    (left right : α) :
    (kernel.extend base).multiplicative.mul left right =
      signedMul base kernel left right :=
  rfl

end NonnegativeMultiplicationKernel

end Foundations.Algebra
