module

public import Std

set_option autoImplicit false

/-!
# Countable bijections and natural pairing

Defines universe-polymorphic bijections, Cantor pairing on `Nat × Nat` with
stepwise and diagonal characterizations, decoder bounds, and the canonical
`Bijection Nat (Nat × Nat)`.
-/

namespace Problib.Countable

universe u v

/-- A universe-polymorphic bijection between two types, given by mutually inverse maps. -/
public structure Bijection (α : Type u) (β : Type v) where
  forward : α → β
  inverse : β → α
  inverse_forward : ∀ value, inverse (forward value) = value
  forward_inverse : ∀ value, forward (inverse value) = value

namespace Pair

/-- Diagonal triangular number $\Delta(n) = n(n+1)/2$, giving the start index of the $n$-th diagonal. -/
@[expose] public def diagonal : Nat → Nat
  | 0 => 0
  | index + 1 => diagonal index + index + 1

/-- Cantor pairing encoding mapping a pair $(i, j) \in \mathbb{N} \times \mathbb{N}$ to a single natural number. -/
@[expose] public def encode (pair : Nat × Nat) : Nat :=
  diagonal (pair.1 + pair.2) + pair.1

/-- Successor step on pairs traversing diagonal lines. -/
@[expose] public def next : Nat × Nat → Nat × Nat
  | (first, 0) => (0, first + 1)
  | (first, second + 1) => (first + 1, second)

/-- Decoding map from a natural index to a pair $(i, j)$ by iterating `next`. -/
@[expose] public def decode : Nat → Nat × Nat
  | 0 => (0, 0)
  | index + 1 => next (decode index)

public theorem diagonal_step (index : Nat) :
    diagonal (index + 1) = diagonal index + index + 1 :=
  rfl

public theorem diagonal_step_strict (index : Nat) :
    diagonal index < diagonal (index + 1) := by
  rw [diagonal_step]
  omega

public theorem diagonal_monotone {left right : Nat}
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
          (Nat.le_of_lt (diagonal_step_strict right))

public theorem diagonal_strict_monotone {left right : Nat}
    (included : left < right) :
    diagonal left < diagonal right :=
  Nat.lt_of_lt_of_le (diagonal_step_strict left)
    (diagonal_monotone (by omega))

public theorem encode_next (pair : Nat × Nat) :
    encode (next pair) = encode pair + 1 := by
  cases pair with
  | mk first second =>
      cases second with
      | zero =>
          simp only [next, encode, Nat.add_zero, Nat.zero_add]
          rw [diagonal_step]
      | succ second =>
          simp only [next, encode]
          have sameDiagonal :
              first + 1 + second = first + (second + 1) := by
            omega
          rw [sameDiagonal]
          omega

/-- Decoding followed by encoding is the identity on natural numbers. -/
public theorem encode_decode (index : Nat) :
    encode (decode index) = index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rw [decode, encode_next, induction]

public theorem encode_lower (pair : Nat × Nat) :
    diagonal (pair.1 + pair.2) ≤ encode pair := by
  unfold encode
  omega

public theorem encode_upper (pair : Nat × Nat) :
    encode pair < diagonal (pair.1 + pair.2 + 1) := by
  rw [diagonal_step]
  unfold encode
  omega

public theorem encode_injective {left right : Nat × Nat}
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
              have diagonalIncluded := diagonal_monotone separated
              have leftLower := encode_lower (leftFirst, leftSecond)
              have rightUpper := encode_upper (rightFirst, rightSecond)
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
              have diagonalIncluded := diagonal_monotone separated
              have leftUpper := encode_upper (leftFirst, leftSecond)
              have rightLower := encode_lower (rightFirst, rightSecond)
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

/-- Encoding followed by decoding is the identity on pairs of natural numbers. -/
public theorem decode_encode (pair : Nat × Nat) :
    decode (encode pair) = pair := by
  apply encode_injective
  exact encode_decode (encode pair)

/-- Both components of a decoded index are bounded by the index itself. -/
public theorem decode_bounds (index : Nat) :
    (decode index).1 ≤ index ∧ (decode index).2 ≤ index := by
  induction index with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ index induction =>
      rw [decode]
      cases equal : decode index with
      | mk first second =>
          rw [equal] at induction
          cases second with
          | zero =>
              simp only [next] at *
              omega
          | succ second =>
              simp only [next] at *
              omega

/-- The first component of a decoded index is bounded by the index itself. -/
public theorem decode_first_le (index : Nat) : (decode index).1 ≤ index :=
  (decode_bounds index).1

/-- The second component of a decoded index is bounded by the index itself. -/
public theorem decode_second_le (index : Nat) : (decode index).2 ≤ index :=
  (decode_bounds index).2

/-- Each component of a pair is at most its code. -/
public theorem le_encode (pair : Nat × Nat) : pair.1 ≤ encode pair ∧ pair.2 ≤ encode pair := by
  have grows : ∀ index, index ≤ diagonal index := by
    intro index
    induction index with
    | zero => exact Nat.le_refl 0
    | succ index induction => rw [diagonal_step]; omega
  have := grows (pair.1 + pair.2)
  unfold encode
  omega

/-- Code a finite list: zero when empty, one past the pair of head and rest
otherwise. -/
@[expose] public def encodeList : List Nat → Nat
  | [] => 0
  | head :: tail => encode (head, encodeList tail) + 1

public theorem encodeList_injective : Function.Injective encodeList := by
  intro left
  induction left with
  | nil => intro right equal; cases right <;> simp [encodeList] at equal ⊢
  | cons head tail induction =>
      intro right equal
      cases right with
      | nil => simp [encodeList] at equal
      | cons other rest =>
          obtain ⟨same, sameTail⟩ := Prod.mk.inj (encode_injective (Nat.succ.inj equal))
          rw [same, induction sameTail]

/-- Code a tuple of fixed length by pairing its first entry with the rest. -/
@[expose] public def encodeTuple : (length : Nat) → (Fin length → Nat) → Nat
  | 0, _ => 0
  | length + 1, entries => encode (entries 0, encodeTuple length (fun index => entries index.succ))

public theorem encodeTuple_injective (length : Nat) :
    Function.Injective (encodeTuple length) := by
  induction length with
  | zero => intro left right _; funext index; exact index.elim0
  | succ length induction =>
      intro left right equal
      have pair := encode_injective equal
      have rest := induction (congrArg Prod.snd pair)
      funext index
      cases index using Fin.cases with
      | zero => exact congrArg Prod.fst pair
      | succ index => exact congrFun rest index

/-- Each entry of a tuple is at most the tuple's code. -/
public theorem le_encodeTuple : (length : Nat) → (entries : Fin length → Nat) → (index : Fin length) →
    entries index ≤ encodeTuple length entries
  | 0, _, index => index.elim0
  | length + 1, entries, index => by
      have bound := le_encode (entries 0, encodeTuple length (fun index => entries index.succ))
      cases index using Fin.cases with
      | zero => exact bound.1
      | succ index =>
          exact Nat.le_trans (le_encodeTuple length (fun index => entries index.succ) index) bound.2

end Pair

/-- Canonical bijection between `Nat` and `Nat × Nat` through Cantor pairing. -/
@[expose] public def pairBijection : Bijection Nat (Nat × Nat) where
  forward := Pair.decode
  inverse := Pair.encode
  inverse_forward := Pair.encode_decode
  forward_inverse := Pair.decode_encode

end Problib.Countable
