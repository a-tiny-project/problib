module

public import Problib.Domain.Order

namespace Problib.Domain

public section

universe u

structure Pointed {α : Type u} (D : CPO α) where
  bottom : α
  below : ∀ x, D.le bottom x

namespace Pointed

variable {α : Type u} {D : CPO α}

@[expose] def iterate (P : Pointed D) (f : α → α) : Nat → α
  | 0 => P.bottom
  | n + 1 => f (P.iterate f n)

theorem iterate_step (P : Pointed D) {f : α → α}
    (hm : ∀ {x y}, D.le x y → D.le (f x) (f y)) (n : Nat) :
    D.le (P.iterate f n) (P.iterate f (n + 1)) := by
  induction n with
  | zero => exact P.below _
  | succ n ih => exact hm ih

theorem iterate_chain (P : Pointed D) {f : α → α}
    (hm : ∀ {x y}, D.le x y → D.le (f x) (f y)) : D.Chain (P.iterate f) := by
  intro i j h
  induction h with
  | refl => exact D.refl _
  | @step j h ih => exact D.trans ih (P.iterate_step hm j)

@[expose] def fix (P : Pointed D) (f : α → α) (hf : D.Continuous D f) : α :=
  D.sup (P.iterate f) (P.iterate_chain hf.monotone)

theorem fix_unfold (P : Pointed D) {f : α → α} (hf : D.Continuous D f) :
    f (P.fix f hf) = P.fix f hf := by
  unfold fix
  rw [hf.preserves]
  apply D.antisymm
  · apply D.sup_least
    intro n
    exact D.below_sup (P.iterate f) _ (n + 1)
  · apply D.sup_least
    intro n
    cases n with
    | zero => exact P.below _
    | succ n => exact D.below_sup (fun n => f (P.iterate f n)) _ n

theorem fix_least_prefixed (P : Pointed D) {f : α → α} (hf : D.Continuous D f)
    (x : α) (hx : D.le (f x) x) : D.le (P.fix f hf) x := by
  apply D.sup_least
  intro n
  induction n with
  | zero => exact P.below x
  | succ n ih => exact D.trans (hf.monotone ih) hx

theorem fix_least (P : Pointed D) {f : α → α} (hf : D.Continuous D f)
    (x : α) (hx : f x = x) : D.le (P.fix f hf) x :=
  P.fix_least_prefixed hf x (by rw [hx]; exact D.refl x)

end Pointed

namespace CPO

variable {α : Type u}

@[expose] def Admissible (D : CPO α) (predicate : α → Prop) : Prop :=
  ∀ c hc, (∀ n, predicate (c n)) → predicate (D.sup c hc)

theorem admissible_le (D : CPO α) (x : α) : D.Admissible (fun y => D.le y x) :=
  fun _ _ h => D.sup_least _ _ x h

end CPO

theorem Pointed.fix_induction {α : Type u} {D : CPO α} (P : Pointed D)
    {f : α → α} (hf : D.Continuous D f) {predicate : α → Prop}
    (admissible : D.Admissible predicate) (base : predicate P.bottom)
    (step : ∀ x, predicate x → predicate (f x)) : predicate (P.fix f hf) := by
  apply admissible
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step _ ih

@[expose] def Pointed.powerset (α : Type u) : Pointed (CPO.powerset α) where
  bottom := fun _ => False
  below := fun _ _ h => h.elim

end

end Problib.Domain
