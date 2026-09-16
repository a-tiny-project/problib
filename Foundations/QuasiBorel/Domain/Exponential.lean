module

public import Foundations.QuasiBorel.Domain.Space

namespace Foundations.QuasiBorel.Domain.Predomain

public section

universe u

open Foundations.Domain

variable {Ω : Type u} {source : Source Ω}

@[expose] def homSup (D E : Predomain source) (c : Nat → Hom D E)
    (hc : ∀ x, E.order.Chain (fun n => c n x)) : Hom D E :=
  ⟨{ toFun := fun x => E.order.sup (fun n => c n x) (hc x)
     mapRandom := fun {random} hr => E.randomSup (fun n seed => c n (random seed))
       (fun seed => hc (random seed)) (fun n => (c n).val.mapRandom hr) },
   CPO.continuous_sup (fun n => (c n).val.toFun) (fun n => (c n).property) hc⟩

@[expose] def homOrder (D E : Predomain source) : CPO (Hom D E) where
  le := fun f g => ∀ x, E.order.le (f x) (g x)
  refl := fun f x => E.order.refl (f x)
  trans := fun h k x => E.order.trans (h x) (k x)
  antisymm := fun h k => Hom.ext (fun x => E.order.antisymm (h x) (k x))
  sup := fun c hc => homSup D E c (fun x i j h => hc i j h x)
  belowSup := fun c _ n x => E.order.belowSup (fun n => c n x) _ n
  supLeast := fun _ _ b h x => E.order.supLeast _ _ (b x) (fun n => h n x)

@[expose] def exponential (D E : Predomain source) : Predomain source where
  space := (Space.exponential D.space E.space).subtype
    (fun f => D.order.Continuous E.order f.toFun)
  order := homOrder D E
  randomSup := by
    intro c hc hr pair hp
    exact E.randomSup (fun n seed => (c n (pair seed).1).val.toFun (pair seed).2)
      (fun seed i j h => hc (pair seed).1 i j h (pair seed).2)
      (fun n => hr n hp)

@[expose] def forgetContinuous (D E : Predomain source) (f : Hom D E) :
    CPO.Hom D.order E.order := ⟨f.val.toFun, f.property⟩

 theorem continuous_forget (D E : Predomain source) :
    (homOrder D E).Continuous (D.order.function E.order) (forgetContinuous D E) where
  monotone := fun h => h
  preserves := fun _ _ => rfl

@[expose] def evaluate (D E : Predomain source) : Hom (product (exponential D E) D) E :=
  ⟨{ toFun := fun p => p.1.val.toFun p.2
     mapRandom := fun {random} hr => hr.1
       (randomPair := fun seed => (seed, (random seed).2)) ⟨source.identity, hr.2⟩ },
   (CPO.continuous_evaluate D.order E.order).comp
     (((continuous_forget D E).comp (CPO.continuous_first _ _)).pair
       (CPO.continuous_second _ _))⟩

@[expose] def curry {D E F : Predomain source} (f : Hom (product D E) F) :
    Hom D (exponential E F) := by
  let g : QuasiBorel.Hom D.space (exponential E F).space :=
    (Space.curry f.val).subtypeLift _ (fun x =>
      f.property.comp ((CPO.Continuous.constant E.order D.order x).pair
        (CPO.Continuous.identity E.order)))
  refine ⟨g, ?_⟩
  refine { monotone := ?_, preserves := ?_ }
  · intro x y h z
    exact f.property.monotone ⟨h, E.order.refl z⟩
  · intro c hc
    apply Hom.ext
    intro y
    have h := f.property.preserves (fun n => (c n, y))
      (fun i j h => ⟨hc i j h, E.order.refl y⟩)
    change f.val (D.order.sup c hc, y) = F.order.sup (fun n => f.val (c n, y)) _
    simpa only [product, CPO.product, E.order.sup_const] using h

@[expose] def uncurry {D E F : Predomain source} (f : Hom D (exponential E F)) :
    Hom (product D E) F :=
  Hom.comp (evaluate E F) (pair (Hom.comp f (first D E)) (second D E))

 theorem uncurry_curry {D E F : Predomain source} (f : Hom (product D E) F) :
    uncurry (curry f) = f := Hom.ext (fun _ => rfl)

 theorem curry_uncurry {D E F : Predomain source} (f : Hom D (exponential E F)) :
    curry (uncurry f) = f := Hom.ext (fun _ => Hom.ext (fun _ => rfl))

 theorem curry_unique {D E F : Predomain source} (f : Hom (product D E) F)
    (g : Hom D (exponential E F)) (h : uncurry g = f) : g = curry f := by
  rw [← h, curry_uncurry]

end

end Foundations.QuasiBorel.Domain.Predomain
