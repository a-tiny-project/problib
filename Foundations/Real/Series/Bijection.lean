module

public import Std

set_option autoImplicit false

namespace Foundations.Real

public structure Bijection (α β : Type) where
  forward : α → β
  inverse : β → α
  inverseForward : ∀ value, inverse (forward value) = value
  forwardInverse : ∀ value, forward (inverse value) = value

namespace NatProductBijection

@[expose] public def diagonal : Nat → Nat
  | 0 => 0
  | index + 1 => diagonal index + index + 1

@[expose] public def encode (pair : Nat × Nat) : Nat :=
  diagonal (pair.1 + pair.2) + pair.1

@[expose] public def next : Nat × Nat → Nat × Nat
  | (first, 0) => (0, first + 1)
  | (first, second + 1) => (first + 1, second)

@[expose] public def decode : Nat → Nat × Nat
  | 0 => (0, 0)
  | index + 1 => next (decode index)

public theorem diagonalStep (index : Nat) :
    diagonal (index + 1) = diagonal index + index + 1 :=
  rfl

public theorem diagonalStepStrict (index : Nat) :
    diagonal index < diagonal (index + 1) := by
  rw [diagonalStep]
  omega

public theorem diagonalMonotone {left right : Nat}
    (included : left ≤ right) :
    diagonal left ≤ diagonal right := by
  induction right with
  | zero =>
      have equal : left = 0 := by omega
      rw [equal]
      exact Nat.le_refl _
  | succ right induction =>
      by_cases equal : left = right + 1
      · rw [equal]
        exact Nat.le_refl _
      · have before : left ≤ right := by omega
        exact Nat.le_trans (induction before)
          (Nat.le_of_lt (diagonalStepStrict right))

public theorem diagonalStrictMonotone {left right : Nat}
    (included : left < right) :
    diagonal left < diagonal right :=
  Nat.lt_of_lt_of_le (diagonalStepStrict left)
    (diagonalMonotone (by omega))

public theorem encodeNext (pair : Nat × Nat) :
    encode (next pair) = encode pair + 1 := by
  cases pair with
  | mk first second =>
      cases second with
      | zero =>
          simp only [next, encode, Nat.add_zero, Nat.zero_add]
          rw [diagonalStep]
      | succ second =>
          simp only [next, encode]
          have sameDiagonal :
              first + 1 + second = first + (second + 1) := by
            omega
          rw [sameDiagonal]
          omega

public theorem encodeDecode (index : Nat) :
    encode (decode index) = index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rw [decode, encodeNext, induction]

public theorem encodeLower (pair : Nat × Nat) :
    diagonal (pair.1 + pair.2) ≤ encode pair := by
  unfold encode
  omega

public theorem encodeUpper (pair : Nat × Nat) :
    encode pair < diagonal (pair.1 + pair.2 + 1) := by
  rw [diagonalStep]
  unfold encode
  omega

public theorem encodeInjective {left right : Nat × Nat}
    (equal : encode left = encode right) :
    left = right := by
  cases left with
  | mk leftFirst leftSecond =>
      cases right with
      | mk rightFirst rightSecond =>
          have sumLe :
              leftFirst + leftSecond ≤ rightFirst + rightSecond := by
            by_cases included :
                leftFirst + leftSecond ≤ rightFirst + rightSecond
            · exact included
            · exfalso
              have separated :
                  rightFirst + rightSecond + 1 ≤
                    leftFirst + leftSecond := by
                omega
              have diagonalIncluded := diagonalMonotone separated
              have leftLower := encodeLower (leftFirst, leftSecond)
              have rightUpper := encodeUpper (rightFirst, rightSecond)
              have strict :
                  encode (rightFirst, rightSecond) <
                    encode (leftFirst, leftSecond) :=
                Nat.lt_of_lt_of_le rightUpper
                  (Nat.le_trans diagonalIncluded leftLower)
              exact (Nat.ne_of_lt strict) equal.symm
          have sumGe :
              rightFirst + rightSecond ≤ leftFirst + leftSecond := by
            by_cases included :
                rightFirst + rightSecond ≤ leftFirst + leftSecond
            · exact included
            · exfalso
              have separated :
                  leftFirst + leftSecond + 1 ≤
                    rightFirst + rightSecond := by
                omega
              have diagonalIncluded := diagonalMonotone separated
              have leftUpper := encodeUpper (leftFirst, leftSecond)
              have rightLower := encodeLower (rightFirst, rightSecond)
              have strict :
                  encode (leftFirst, leftSecond) <
                    encode (rightFirst, rightSecond) :=
                Nat.lt_of_lt_of_le leftUpper
                  (Nat.le_trans diagonalIncluded rightLower)
              exact (Nat.ne_of_lt strict) equal
          have sumEqual :
              leftFirst + leftSecond = rightFirst + rightSecond := by
            omega
          have firstEqual : leftFirst = rightFirst := by
            simp only [encode] at equal
            rw [sumEqual] at equal
            omega
          have secondEqual : leftSecond = rightSecond := by
            omega
          rw [firstEqual, secondEqual]

public theorem decodeEncode (pair : Nat × Nat) :
    decode (encode pair) = pair := by
  apply encodeInjective
  exact encodeDecode (encode pair)

end NatProductBijection

@[expose] public def natProductBijection : Bijection Nat (Nat × Nat) where
  forward := NatProductBijection.decode
  inverse := NatProductBijection.encode
  inverseForward := NatProductBijection.encodeDecode
  forwardInverse := NatProductBijection.decodeEncode

end Foundations.Real
