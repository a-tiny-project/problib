module

public import Std

set_option autoImplicit false

namespace Problib.Domain

public section

universe u v w

structure CPO (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  sup : (c : Nat → α) → (∀ i j, i ≤ j → le (c i) (c j)) → α
  below_sup : ∀ c hc n, le (c n) (sup c hc)
  sup_least : ∀ c hc b, (∀ n, le (c n) b) → le (sup c hc) b

namespace CPO

variable {α : Type u} {β : Type v} {γ : Type w}

abbrev Chain (D : CPO α) (c : Nat → α) : Prop := ∀ i j, i ≤ j → D.le (c i) (c j)

structure Continuous (D : CPO α) (E : CPO β) (f : α → β) : Prop where
  monotone : ∀ {x y}, D.le x y → E.le (f x) (f y)
  preserves : ∀ c hc, f (D.sup c hc) = E.sup (fun n => f (c n))
    (fun i j h => monotone (hc i j h))

theorem sup_const (D : CPO α) (a : α) :
    D.sup (fun _ => a) (fun _ _ _ => D.refl a) = a :=
  D.antisymm (D.sup_least _ _ _ (fun _ => D.refl a)) (D.below_sup (fun _ => a) _ 0)

theorem sup_mono (D : CPO α) {c d : Nat → α} {hc : D.Chain c} {hd : D.Chain d}
    (h : ∀ n, D.le (c n) (d n)) : D.le (D.sup c hc) (D.sup d hd) :=
  D.sup_least _ _ _ (fun n => D.trans (h n) (D.below_sup _ _ n))

theorem Continuous.identity (D : CPO α) : D.Continuous D (fun x => x) :=
  ⟨fun h => h, fun _ _ => rfl⟩

theorem Continuous.constant (D : CPO α) (E : CPO β) (b : β) :
    D.Continuous E (fun _ => b) := ⟨fun _ => E.refl b, fun _ _ => (E.sup_const b).symm⟩

theorem Continuous.comp {D : CPO α} {E : CPO β} {F : CPO γ}
    {f : α → β} {g : β → γ} (hg : E.Continuous F g) (hf : D.Continuous E f) :
    D.Continuous F (fun x => g (f x)) where
  monotone := fun h => hg.monotone (hf.monotone h)
  preserves := by
    intro c hc
    rw [hf.preserves, hg.preserves]

@[expose] def discrete (α : Type u) : CPO α where
  le := Eq
  refl := fun _ => rfl
  trans := Eq.trans
  antisymm := fun h _ => h
  sup := fun c _ => c 0
  below_sup := fun _ hc n => (hc 0 n (Nat.zero_le n)).symm
  sup_least := fun _ _ _ h => h 0

theorem continuous_from_discrete (E : CPO β) (f : α → β) :
    (discrete α).Continuous E f where
  monotone := fun h => h ▸ E.refl _
  preserves := by
    intro c hc
    apply E.antisymm
    · exact E.below_sup (fun n => f (c n)) _ 0
    · apply E.sup_least
      intro n
      rw [← hc 0 n (Nat.zero_le n)]
      exact E.refl _

@[expose] def product (D : CPO α) (E : CPO β) : CPO (α × β) where
  le := fun x y => D.le x.1 y.1 ∧ E.le x.2 y.2
  refl := fun x => ⟨D.refl x.1, E.refl x.2⟩
  trans := fun h k => ⟨D.trans h.1 k.1, E.trans h.2 k.2⟩
  antisymm := fun h k => Prod.ext (D.antisymm h.1 k.1) (E.antisymm h.2 k.2)
  sup := fun c hc => (D.sup (fun n => (c n).1) (fun i j h => (hc i j h).1),
    E.sup (fun n => (c n).2) (fun i j h => (hc i j h).2))
  below_sup := fun c _ n => ⟨D.below_sup (fun n => (c n).1) _ n, E.below_sup (fun n => (c n).2) _ n⟩
  sup_least := fun _ _ b h => ⟨D.sup_least _ _ b.1 (fun n => (h n).1),
    E.sup_least _ _ b.2 (fun n => (h n).2)⟩

@[expose] def pi {ι : Type v} {α : ι → Type u} (D : ∀ i, CPO (α i)) : CPO (∀ i, α i) where
  le := fun f g => ∀ i, (D i).le (f i) (g i)
  refl := fun f i => (D i).refl (f i)
  trans := fun h k i => (D i).trans (h i) (k i)
  antisymm := fun h k => funext (fun i => (D i).antisymm (h i) (k i))
  sup := fun c hc i => (D i).sup (fun n => c n i) (fun n m h => hc n m h i)
  below_sup := fun c _ n i => (D i).below_sup (fun n => c n i) _ n
  sup_least := fun _ _ _ h i => (D i).sup_least _ _ _ (fun n => h n i)

@[expose] def powerset (α : Type u) : CPO (α → Prop) where
  le := fun a b => ∀ x, a x → b x
  refl := fun _ _ h => h
  trans := fun h k x hx => k x (h x hx)
  antisymm := fun h k => funext (fun x => propext ⟨h x, k x⟩)
  sup := fun c _ x => ∃ n, c n x
  below_sup := fun _ _ n _ h => ⟨n, h⟩
  sup_least := fun _ _ _ h x ⟨n, hx⟩ => h n x hx

end CPO

end

end Problib.Domain
