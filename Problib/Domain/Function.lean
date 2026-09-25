module

public import Problib.Domain.FixedPoint

namespace Problib.Domain.CPO

public section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

 theorem continuous_sup {D : CPO α} {E : CPO β} (f : Nat → α → β)
    (hf : ∀ n, D.Continuous E (f n))
    (hc : ∀ x, E.Chain (fun n => f n x)) :
    D.Continuous E (fun x => E.sup (fun n => f n x) (hc x)) where
  monotone := fun h => E.sup_mono (fun n => (hf n).monotone h)
  preserves := by
    intro c hd
    apply E.antisymm
    · apply E.sup_least
      intro n
      rw [(hf n).preserves]
      apply E.sup_least
      intro m
      exact E.trans (E.below_sup (fun n => f n (c m)) _ n)
        (E.below_sup (fun m => E.sup (fun n => f n (c m)) (hc (c m))) _ m)
    · apply E.sup_least
      intro m
      apply E.sup_least
      intro n
      exact E.trans ((hf n).monotone (D.below_sup c hd m))
        (E.below_sup (fun n => f n (D.sup c hd)) _ n)

@[expose] def subtype (D : CPO α) (p : α → Prop) (hp : D.Admissible p) :
    CPO {x // p x} where
  le := fun x y => D.le x.val y.val
  refl := fun x => D.refl x.val
  trans := D.trans
  antisymm := fun h k => Subtype.ext (D.antisymm h k)
  sup := fun c hc => ⟨D.sup (fun n => (c n).val) hc, hp _ hc (fun n => (c n).property)⟩
  below_sup := fun c _ n => D.below_sup (fun n => (c n).val) _ n
  sup_least := fun _ _ b h => D.sup_least _ _ b.val h

abbrev Hom (D : CPO α) (E : CPO β) := {f : α → β // D.Continuous E f}

@[expose] def function (D : CPO α) (E : CPO β) : CPO (Hom D E) :=
  (pi (fun _ : α => E)).subtype (fun f => D.Continuous E f)
    (fun c hc hf => continuous_sup c hf (fun x i j h => hc i j h x))

 theorem continuous_first (D : CPO α) (E : CPO β) :
    (D.product E).Continuous D Prod.fst := ⟨fun h => h.1, fun _ _ => rfl⟩

 theorem continuous_second (D : CPO α) (E : CPO β) :
    (D.product E).Continuous E Prod.snd := ⟨fun h => h.2, fun _ _ => rfl⟩

 theorem Continuous.pair {D : CPO α} {E : CPO β} {F : CPO γ}
    {f : α → β} {g : α → γ} (hf : D.Continuous E f) (hg : D.Continuous F g) :
    D.Continuous (E.product F) (fun x => (f x, g x)) where
  monotone := fun h => ⟨hf.monotone h, hg.monotone h⟩
  preserves := fun c hc => Prod.ext (hf.preserves c hc) (hg.preserves c hc)

 theorem continuous_evaluate (D : CPO α) (E : CPO β) :
    ((function D E).product D).Continuous E (fun p => p.1.val p.2) where
  monotone := fun {x y} h => E.trans (h.1 x.2) (y.1.property.monotone h.2)
  preserves := by
    intro c hc
    apply E.antisymm
    · apply E.sup_least
      intro n
      change E.le ((c n).1.val (D.sup (fun n => (c n).2) _)) _
      rw [(c n).1.property.preserves]
      apply E.sup_least
      intro m
      exact E.trans
        (E.trans ((hc n (max n m) (Nat.le_max_left n m)).1 ((c m).2))
          ((c (max n m)).1.property.monotone
            ((hc m (max n m) (Nat.le_max_right n m)).2)))
        (E.below_sup (fun k => (c k).1.val (c k).2) _ (max n m))
    · apply E.sup_least
      intro n
      exact E.trans ((c n).1.property.monotone
        (D.below_sup (fun n => (c n).2) _ n))
        (E.below_sup (fun n => (c n).1.val
          (D.sup (fun n => (c n).2) (fun i j h => (hc i j h).2))) _ n)

@[expose] def curry {D : CPO α} {E : CPO β} {F : CPO γ}
    (f : Hom (D.product E) F) (x : α) : Hom E F :=
  ⟨fun y => f.val (x, y), f.property.comp
    ((Continuous.constant E D x).pair (Continuous.identity E))⟩

 theorem continuous_curry {D : CPO α} {E : CPO β} {F : CPO γ}
    (f : Hom (D.product E) F) : D.Continuous (function E F) (curry f) where
  monotone := fun {x y} h z => f.property.monotone ⟨h, E.refl z⟩
  preserves := by
    intro c hc
    apply Subtype.ext
    funext y
    have h := f.property.preserves (fun n => (c n, y))
      (fun i j h => ⟨hc i j h, E.refl y⟩)
    change f.val (D.sup c hc, y) = F.sup (fun n => f.val (c n, y)) _
    simpa only [product, E.sup_const] using h

end

end Problib.Domain.CPO
