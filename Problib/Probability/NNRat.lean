import Init.Data.Rat.Lemmas

namespace Problib.Probability

structure NNRat where
  val : Rat
  nonnegative : 0 ≤ val
deriving Repr, DecidableEq

namespace NNRat

instance : Coe NNRat Rat where
  coe := NNRat.val

@[ext] theorem ext {a b : NNRat} (h : (a : Rat) = (b : Rat)) : a = b := by
  cases a
  cases b
  cases h
  rfl

def ofRat (q : Rat) (h : 0 ≤ q) : NNRat :=
  ⟨q, h⟩

instance : Zero NNRat where
  zero := ⟨0, by decide⟩

instance : One NNRat where
  one := ⟨1, Rat.natCast_nonneg⟩

instance : Add NNRat where
  add a b := ⟨(a : Rat) + (b : Rat), Rat.add_nonneg a.nonnegative b.nonnegative⟩

instance : Mul NNRat where
  mul a b := ⟨(a : Rat) * (b : Rat), Rat.mul_nonneg a.nonnegative b.nonnegative⟩

@[simp] theorem val_zero : ((0 : NNRat) : Rat) = 0 := rfl

@[simp] theorem val_one : ((1 : NNRat) : Rat) = 1 := rfl

@[simp] theorem val_add (a b : NNRat) : ((a + b : NNRat) : Rat) = (a : Rat) + (b : Rat) := rfl

@[simp] theorem val_mul (a b : NNRat) : ((a * b : NNRat) : Rat) = (a : Rat) * (b : Rat) := rfl

@[simp] theorem zero_add (a : NNRat) : 0 + a = a :=
  ext (Rat.zero_add (a : Rat))

@[simp] theorem add_zero (a : NNRat) : a + 0 = a :=
  ext (Rat.add_zero (a : Rat))

theorem add_comm (a b : NNRat) : a + b = b + a :=
  ext (Rat.add_comm (a : Rat) (b : Rat))

theorem add_assoc (a b c : NNRat) : a + b + c = a + (b + c) :=
  ext (Rat.add_assoc (a : Rat) (b : Rat) (c : Rat))

theorem add_left_comm (a b c : NNRat) : a + (b + c) = b + (a + c) := by
  apply ext
  change (a : Rat) + ((b : Rat) + (c : Rat)) = (b : Rat) + ((a : Rat) + (c : Rat))
  rw [← Rat.add_assoc, Rat.add_comm (a : Rat) (b : Rat), Rat.add_assoc]

theorem add_add_add_comm (a b c d : NNRat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, add_left_comm b c d, ← add_assoc]

@[simp] theorem zero_mul (a : NNRat) : 0 * a = 0 :=
  ext (Rat.zero_mul (a : Rat))

@[simp] theorem mul_zero (a : NNRat) : a * 0 = 0 :=
  ext (Rat.mul_zero (a : Rat))

@[simp] theorem one_mul (a : NNRat) : 1 * a = a :=
  ext (Rat.one_mul (a : Rat))

@[simp] theorem mul_one (a : NNRat) : a * 1 = a :=
  ext (Rat.mul_one (a : Rat))

theorem mul_comm (a b : NNRat) : a * b = b * a :=
  ext (Rat.mul_comm (a : Rat) (b : Rat))

theorem mul_assoc (a b c : NNRat) : a * b * c = a * (b * c) :=
  ext (Rat.mul_assoc (a : Rat) (b : Rat) (c : Rat))

theorem mul_left_comm (a b c : NNRat) : a * (b * c) = b * (a * c) := by
  apply ext
  change (a : Rat) * ((b : Rat) * (c : Rat)) = (b : Rat) * ((a : Rat) * (c : Rat))
  rw [← Rat.mul_assoc, Rat.mul_comm (a : Rat) (b : Rat), Rat.mul_assoc]

theorem mul_mul_mul_comm (a b c d : NNRat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mul_assoc, mul_left_comm b c d, ← mul_assoc]

theorem add_mul (a b c : NNRat) : (a + b) * c = a * c + b * c :=
  ext (Rat.add_mul (a : Rat) (b : Rat) (c : Rat))

theorem mul_add (a b c : NNRat) : a * (b + c) = a * b + a * c :=
  ext (Rat.mul_add (a : Rat) (b : Rat) (c : Rat))

theorem val_ne_zero_of_ne_zero {a : NNRat} (h : a ≠ 0) : (a : Rat) ≠ 0 := by
  intro hzero
  apply h
  exact ext hzero

theorem mul_ne_zero {a b : NNRat} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro zero
  have valuesZero := congrArg NNRat.val zero
  rcases Rat.mul_eq_zero.mp valuesZero with leftZero | rightZero
  · exact ha (ext leftZero)
  · exact hb (ext rightZero)

theorem mul_left_cancel {a b c : NNRat} (ha : a ≠ 0)
    (equal : a * b = a * c) : b = c := by
  apply ext
  have valuesEqual := congrArg NNRat.val equal
  have haVal := val_ne_zero_of_ne_zero ha
  calc
    (b : Rat) = ((a : Rat)⁻¹ * (a : Rat)) * (b : Rat) := by
      rw [Rat.inv_mul_cancel _ haVal, Rat.one_mul]
    _ = (a : Rat)⁻¹ * ((a : Rat) * (b : Rat)) :=
      Rat.mul_assoc _ _ _
    _ = (a : Rat)⁻¹ * ((a : Rat) * (c : Rat)) :=
      congrArg (fun value => (a : Rat)⁻¹ * value) valuesEqual
    _ = ((a : Rat)⁻¹ * (a : Rat)) * (c : Rat) :=
      (Rat.mul_assoc _ _ _).symm
    _ = (c : Rat) := by
      rw [Rat.inv_mul_cancel _ haVal, Rat.one_mul]

def inverse (a : NNRat) (h : a ≠ 0) : NNRat := by
  refine ⟨(a : Rat)⁻¹, ?_⟩
  have hpositive : 0 < (a : Rat) := Rat.lt_of_le_of_ne a.nonnegative (by
    intro hzero
    exact val_ne_zero_of_ne_zero h hzero.symm)
  exact Rat.le_of_lt (Rat.inv_pos.mpr hpositive)

@[simp] theorem val_inverse (a : NNRat) (h : a ≠ 0) :
    ((inverse a h : NNRat) : Rat) = (a : Rat)⁻¹ := rfl

theorem inverse_mul_self (a : NNRat) (h : a ≠ 0) : inverse a h * a = 1 :=
  ext (Rat.inv_mul_cancel (a : Rat) (val_ne_zero_of_ne_zero h))

theorem mul_inverse_self (a : NNRat) (h : a ≠ 0) : a * inverse a h = 1 :=
  ext (Rat.mul_inv_cancel (a : Rat) (val_ne_zero_of_ne_zero h))

end NNRat

end Problib.Probability
