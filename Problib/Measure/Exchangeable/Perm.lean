module

public import Problib.Countable.Bijection

set_option autoImplicit false

/-!
# Permutations of finite slots

A permutation of `n` slots is a bijection of `Fin n`. `skip i` embeds the `n`
slots other than `i` into `n + 1` slots in order, and `unskip i` is its inverse
off `i`. `removeAt σ i` is the permutation σ induces once slot `i` of its target
and slot `σ⁻¹ i` of its source are removed; `removeAt_spec` is the identity a
view's deletion law needs. `toLast i` moves slot `i` to the last slot and keeps
the order of the others.
-/

namespace Problib.Measure.Exchangeable

public section

/-- A permutation of `n` slots. -/
abbrev Perm (n : Nat) := Countable.Bijection (Fin n) (Fin n)

variable {n : Nat}

/-- The slot of `n + 1` that slot `j` of the `n` slots other than `i` occupies. -/
@[expose] def skip (i : Fin (n + 1)) (j : Fin n) : Fin (n + 1) :=
  if j.val < i.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

theorem skip_val (i : Fin (n + 1)) (j : Fin n) :
    (skip i j).val = if j.val < i.val then j.val else j.val + 1 := by
  unfold skip; split <;> rfl

/-- The slot among the `n` slots other than `i` that slot `j ≠ i` of `n + 1`
occupies. -/
@[expose] def unskip (i j : Fin (n + 1)) (different : j ≠ i) : Fin n :=
  if below : j.val < i.val then ⟨j.val, by omega⟩
  else ⟨j.val - 1, by
    have : j.val ≠ i.val := fun equal => different (Fin.ext equal)
    omega⟩

theorem unskip_val (i j : Fin (n + 1)) (different : j ≠ i) :
    (unskip i j different).val = if j.val < i.val then j.val else j.val - 1 := by
  unfold unskip; split <;> rfl

theorem skip_ne (i : Fin (n + 1)) (j : Fin n) : skip i j ≠ i := by
  intro equal
  have := congrArg Fin.val equal
  rw [skip_val] at this
  split at this <;> omega

theorem skip_unskip (i j : Fin (n + 1)) (different : j ≠ i) :
    skip i (unskip i j different) = j := by
  have : j.val ≠ i.val := fun equal => different (Fin.ext equal)
  apply Fin.ext
  rw [skip_val, unskip_val]
  by_cases below : j.val < i.val
  · simp only [below, ite_true]
  · have after : ¬ j.val - 1 < i.val := by omega
    simp only [below, after, ite_false]
    omega

theorem unskip_skip (i : Fin (n + 1)) (j : Fin n) (different : skip i j ≠ i) :
    unskip i (skip i j) different = j := by
  apply Fin.ext
  rw [unskip_val, skip_val]
  by_cases below : j.val < i.val
  · simp only [below, ite_true]
  · have after : ¬ j.val + 1 < i.val := by omega
    simp only [below, after, ite_false]
    omega

theorem skip_injective (i : Fin (n + 1)) {j k : Fin n} (equal : skip i j = skip i k) : j = k := by
  rw [← unskip_skip i j (skip_ne i j), ← unskip_skip i k (skip_ne i k)]
  congr 1

theorem unskip_congr (i : Fin (n + 1)) {j k : Fin (n + 1)} (equal : j = k)
    (left : j ≠ i) (right : k ≠ i) : unskip i j left = unskip i k right := by
  subst equal; rfl


namespace Perm

/-- The identity permutation. -/
@[expose] def id (n : Nat) : Perm n where
  forward := fun index => index
  inverse := fun index => index
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl

/-- The inverse permutation. -/
@[expose] def symm (σ : Perm n) : Perm n where
  forward := σ.inverse
  inverse := σ.forward
  inverse_forward := σ.forward_inverse
  forward_inverse := σ.inverse_forward

/-- `σ` after `τ`. -/
@[expose] def comp (σ τ : Perm n) : Perm n where
  forward := fun index => σ.forward (τ.forward index)
  inverse := fun index => τ.inverse (σ.inverse index)
  inverse_forward := fun index => by rw [σ.inverse_forward, τ.inverse_forward]
  forward_inverse := fun index => by rw [τ.forward_inverse, σ.forward_inverse]

theorem inverse_injective (σ : Perm n) {i j : Fin n} (equal : σ.inverse i = σ.inverse j) :
    i = j := by
  rw [← σ.forward_inverse i, ← σ.forward_inverse j, equal]

theorem forward_injective (σ : Perm n) {i j : Fin n} (equal : σ.forward i = σ.forward j) :
    i = j := by
  rw [← σ.inverse_forward i, ← σ.inverse_forward j, equal]

theorem removeAt_forward_ne (σ : Perm (n + 1)) (i : Fin (n + 1)) (j : Fin n) :
    σ.forward (skip (σ.inverse i) j) ≠ i := by
  intro equal
  have back := congrArg σ.inverse equal
  rw [σ.inverse_forward] at back
  exact skip_ne _ _ back

theorem removeAt_inverse_ne (σ : Perm (n + 1)) (i : Fin (n + 1)) (j : Fin n) :
    σ.inverse (skip i j) ≠ σ.inverse i :=
  fun equal => skip_ne i j (inverse_injective σ equal)

/-- The permutation σ induces on the slots other than `i`: slot `j` of the
remaining `n` goes where σ sends the matching slot of `n + 1`, with `i` removed
from the target and its preimage removed from the source. -/
@[expose] def removeAt (σ : Perm (n + 1)) (i : Fin (n + 1)) : Perm n where
  forward := fun j => unskip i (σ.forward (skip (σ.inverse i) j)) (removeAt_forward_ne σ i j)
  inverse := fun j => unskip (σ.inverse i) (σ.inverse (skip i j)) (removeAt_inverse_ne σ i j)
  inverse_forward := fun j => by
    have equal : σ.inverse (skip i (unskip i (σ.forward (skip (σ.inverse i) j))
        (removeAt_forward_ne σ i j))) = skip (σ.inverse i) j := by
      rw [skip_unskip, σ.inverse_forward]
    rw [unskip_congr _ equal _ (skip_ne _ _), unskip_skip]
  forward_inverse := fun j => by
    have equal : σ.forward (skip (σ.inverse i) (unskip (σ.inverse i) (σ.inverse (skip i j))
        (removeAt_inverse_ne σ i j))) = skip i j := by
      rw [skip_unskip, σ.forward_inverse]
    rw [unskip_congr _ equal _ (skip_ne _ _), unskip_skip]

theorem removeAt_spec (σ : Perm (n + 1)) (i : Fin (n + 1)) (j : Fin n) :
    skip (σ.inverse i) ((σ.removeAt i).inverse j) = σ.inverse (skip i j) :=
  skip_unskip _ _ (removeAt_inverse_ne σ i j)

/-- The permutation that moves slot `i` to the last slot and keeps the order of
the others. -/
@[expose] def toLast (i : Fin (n + 1)) : Perm (n + 1) where
  forward := fun j => if same : j = i then Fin.last n else (unskip i j same).castSucc
  inverse := fun k => if below : k.val < n then skip i ⟨k.val, below⟩ else i
  inverse_forward := fun j => by
    by_cases same : j = i
    · simp [same]
    · have below : ((unskip i j same).castSucc).val < n := (unskip i j same).isLt
      simp only [same, dite_false, below, dite_true]
      have equal : (⟨(unskip i j same).castSucc.val, below⟩ : Fin n) = unskip i j same :=
        Fin.ext rfl
      rw [equal, skip_unskip]
  forward_inverse := fun k => by
    by_cases below : k.val < n
    · simp only [below, dite_true, skip_ne, dite_false]
      apply Fin.ext
      rw [Fin.val_castSucc, unskip_skip]
    · have last : k = Fin.last n := Fin.ext (by have := k.isLt; simp; omega)
      simp [last]

theorem toLast_inverse_castSucc (i : Fin (n + 1)) (k : Fin n) :
    (toLast i).inverse k.castSucc = skip i k := by
  simp [toLast, k.isLt]

theorem toLast_inverse_last (i : Fin (n + 1)) : (toLast i).inverse (Fin.last n) = i := by
  simp [toLast]

theorem toLast_forward_self (i : Fin (n + 1)) : (toLast i).forward i = Fin.last n := by
  simp [toLast]

end Perm

end

end Problib.Measure.Exchangeable
