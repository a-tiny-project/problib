module

public import Foundations.Domain.Function

namespace Foundations.Domain.Necessity

public section

@[expose] def grow (s : Nat → Prop) : Nat → Prop
  | 0 => True
  | n + 1 => s n

 theorem grow_continuous : (CPO.powerset Nat).Continuous (CPO.powerset Nat) grow where
  monotone := by
    intro s t h n
    cases n with
    | zero => exact fun _ => True.intro
    | succ n => exact h n
  preserves := by
    intro c hc
    funext n
    apply propext
    cases n with
    | zero => exact ⟨fun _ => ⟨0, True.intro⟩, fun _ => True.intro⟩
    | succ n => exact Iff.rfl

 theorem iterate_grow (k n : Nat) :
    (Pointed.powerset Nat).iterate grow k n ↔ n < k := by
  induction k generalizing n with
  | zero => simp [Pointed.iterate, Pointed.powerset]
  | succ k ih =>
    cases n with
    | zero => exact ⟨fun _ => Nat.zero_lt_succ k, fun _ => True.intro⟩
    | succ n => exact (ih n).trans Nat.succ_lt_succ_iff.symm

 theorem grow_fix_all (n : Nat) : (Pointed.powerset Nat).fix grow grow_continuous n :=
  ⟨n + 1, (iterate_grow (n + 1) n).mpr (Nat.lt_succ_self n)⟩

@[expose] def Bounded (s : Nat → Prop) : Prop := ∃ k, ∀ n, s n → n < k

 theorem bounded_bottom : Bounded (Pointed.powerset Nat).bottom :=
  ⟨0, fun _ h => h.elim⟩

 theorem bounded_step {s : Nat → Prop} (h : Bounded s) : Bounded (grow s) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  intro n hn
  cases n with
  | zero => exact Nat.zero_lt_succ k
  | succ n => exact Nat.succ_lt_succ (hk n hn)

 theorem admissibility_necessary : ¬ Bounded ((Pointed.powerset Nat).fix grow grow_continuous) := by
  intro ⟨k, hk⟩
  exact Nat.lt_irrefl k (hk k (grow_fix_all k))

 theorem bounded_not_admissible : ¬ (CPO.powerset Nat).Admissible Bounded := by
  intro h
  exact admissibility_necessary
    ((Pointed.powerset Nat).fix_induction grow_continuous h bounded_bottom
      (fun _ => bounded_step))

@[expose] def jump (s : Nat → Prop) : Nat → Prop
  | 0 => ∀ n, s (n + 1)
  | n + 1 => grow (fun m => s (m + 1)) n

 theorem jump_monotone {s t : Nat → Prop} (h : (CPO.powerset Nat).le s t) :
    (CPO.powerset Nat).le (jump s) (jump t) := by
  intro n hn
  cases n with
  | zero => exact fun m => h (m + 1) (hn m)
  | succ n => exact grow_continuous.monotone (fun m => h (m + 1)) n hn

 theorem iterate_jump (k n : Nat) :
    (Pointed.powerset Nat).iterate jump k n ↔ 0 < n ∧ n ≤ k := by
  induction k generalizing n with
  | zero => constructor <;> intro h <;> simp_all [Pointed.iterate, Pointed.powerset]; omega
  | succ k ih =>
    cases n with
    | zero =>
      change (∀ n, (Pointed.powerset Nat).iterate jump k (n + 1)) ↔ _
      constructor
      · intro h
        have bad := (ih (k + 1)).mp (h k)
        omega
      · intro h
        omega
    | succ n =>
      cases n with
      | zero => exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => True.intro⟩
      | succ n =>
        change (Pointed.powerset Nat).iterate jump k (n + 1) ↔ _
        rw [ih]
        omega

@[expose] def jumpLimit : Nat → Prop :=
  (CPO.powerset Nat).sup ((Pointed.powerset Nat).iterate jump)
    ((Pointed.powerset Nat).iterate_chain jump_monotone)

 theorem jumpLimit_positive (n : Nat) : jumpLimit n ↔ 0 < n := by
  constructor
  · intro ⟨k, hk⟩
    exact ((iterate_jump k n).mp hk).1
  · intro hn
    exact ⟨n, (iterate_jump n n).mpr ⟨hn, Nat.le_refl n⟩⟩

 theorem continuity_necessary : jump jumpLimit ≠ jumpLimit := by
  intro h
  have added : jump jumpLimit 0 := fun n =>
    (jumpLimit_positive (n + 1)).mpr (Nat.zero_lt_succ n)
  have bad : jumpLimit 0 := h ▸ added
  exact Nat.lt_irrefl 0 ((jumpLimit_positive 0).mp bad)

 theorem jump_not_continuous : ¬ (CPO.powerset Nat).Continuous (CPO.powerset Nat) jump := by
  intro h
  exact continuity_necessary ((Pointed.powerset Nat).fix_unfold h)

 theorem pointedness_necessary :
    (CPO.discrete Bool).Continuous (CPO.discrete Bool) Bool.not ∧
      ¬ ∃ x, Bool.not x = x := by
  refine ⟨CPO.continuous_from_discrete _ _, ?_⟩
  intro ⟨x, h⟩
  cases x <;> cases h

 theorem monotonicity_necessary :
    ¬ ∃ s : Unit → Prop, (fun x => ¬ s x) = s := by
  intro ⟨s, h⟩
  have eq : (¬ s ()) = s () := congrFun h ()
  have forward : (¬ s ()) → s () := fun hn => eq ▸ hn
  have backward : s () → ¬ s () := fun hs => eq.symm ▸ hs
  have hn : ¬ s () := fun hs => backward hs hs
  exact hn (forward hn)

 theorem induction_base_necessary :
    (CPO.powerset Unit).Admissible (fun _ => False) ∧
    (∀ _ : Unit → Prop, False → False) ∧
    ¬ (fun _ : Unit → Prop => False)
      ((Pointed.powerset Unit).fix (fun s => s) (CPO.Continuous.identity _)) :=
  ⟨fun _ _ h => h 0, fun _ h => h, fun h => h⟩

 theorem induction_step_necessary :
    (CPO.powerset Unit).Admissible
      (fun s => (CPO.powerset Unit).le s (Pointed.powerset Unit).bottom) ∧
    (CPO.powerset Unit).le (Pointed.powerset Unit).bottom (Pointed.powerset Unit).bottom ∧
    ¬ (CPO.powerset Unit).le
      ((Pointed.powerset Unit).fix (fun _ _ => True) (CPO.Continuous.constant _ _ _))
      (Pointed.powerset Unit).bottom := by
  refine ⟨CPO.admissible_le _ _, (CPO.powerset Unit).refl _, ?_⟩
  intro h
  exact h () ⟨1, True.intro⟩

end

end Foundations.Domain.Necessity
