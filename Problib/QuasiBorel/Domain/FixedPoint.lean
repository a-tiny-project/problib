module

public import Problib.QuasiBorel.Domain.Exponential

namespace Problib.QuasiBorel.Domain.Predomain

public section

universe u v

open Problib.Domain

variable {Ω : Type u} {source : Source Ω}

@[expose] def pointedProduct {D E : Predomain source}
    (p : Pointed D.order) (q : Pointed E.order) : Pointed (product D E).order where
  bottom := (p.bottom, q.bottom)
  below := fun x => ⟨p.below x.1, q.below x.2⟩

@[expose] def pointedPi {ι : Type v} {D : ι → Predomain source}
    (p : ∀ i, Pointed (D i).order) : Pointed (pi D).order where
  bottom := fun i => (p i).bottom
  below := fun x i => (p i).below (x i)

@[expose] def pointedExponential (D E : Predomain source) (p : Pointed E.order) :
    Pointed (exponential D E).order where
  bottom := Hom.constant D E p.bottom
  below := fun f x => p.below (f.val.toFun x)

@[expose] def iterateHom (D : Predomain source) (p : Pointed D.order) :
    Nat → Hom (exponential D D) D
  | 0 => Hom.constant _ D p.bottom
  | n + 1 => Hom.comp (evaluate D D) (pair (Hom.identity _) (iterateHom D p n))

 theorem iterateHom_apply (D : Predomain source) (p : Pointed D.order)
    (n : Nat) (f : Hom D D) : iterateHom D p n f = p.iterate f.val.toFun n := by
  induction n with
  | zero => rfl
  | succ n ih => change f (iterateHom D p n f) = f (p.iterate f.val.toFun n); rw [ih]

@[expose] def fix (D : Predomain source) (p : Pointed D.order) :
    Hom (exponential D D) D :=
  homSup _ D (iterateHom D p) (by
    intro f i j h
    change D.order.le (iterateHom D p i f) (iterateHom D p j f)
    rw [iterateHom_apply, iterateHom_apply]
    exact p.iterate_chain f.property.monotone i j h)

 theorem fix_apply (D : Predomain source) (p : Pointed D.order) (f : Hom D D) :
    fix D p f = p.fix f.val.toFun f.property := by
  change D.order.sup (fun n => iterateHom D p n f) _ = D.order.sup (p.iterate f.val.toFun) _
  have h : (fun n => iterateHom D p n f) = p.iterate f.val.toFun :=
    funext (fun n => iterateHom_apply D p n f)
  simp only [h]

 theorem fix_unfold (D : Predomain source) (p : Pointed D.order) (f : Hom D D) :
    f (fix D p f) = fix D p f := by
  rw [fix_apply]
  exact p.fix_unfold f.property

 theorem fix_least (D : Predomain source) (p : Pointed D.order) (f : Hom D D)
    (x : D.space.Carrier) (h : f x = x) : D.order.le (fix D p f) x := by
  rw [fix_apply]
  exact p.fix_least f.property x h

 theorem fix_induction (D : Predomain source) (p : Pointed D.order) (f : Hom D D)
    {predicate : D.space.Carrier → Prop} (admissible : D.order.Admissible predicate)
    (base : predicate p.bottom) (step : ∀ x, predicate x → predicate (f x)) :
    predicate (fix D p f) := by
  rw [fix_apply]
  exact p.fix_induction f.property admissible base step

end

end Problib.QuasiBorel.Domain.Predomain
