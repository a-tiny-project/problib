module

public import Foundations.Domain.Function
public import Foundations.QuasiBorel.CartesianClosed
public import Foundations.QuasiBorel.Pi
public import Foundations.QuasiBorel.Subtype

namespace Foundations.QuasiBorel.Domain

public section

universe u v w

open Foundations.Domain

structure Predomain {Ω : Type u} (source : Source Ω) where
  space : Space.{u, v} source
  order : CPO space.Carrier
  randomSup : ∀ (c : Nat → Ω → space.Carrier)
    (hc : ∀ seed, order.Chain (fun n => c n seed)),
    (∀ n, space.Random (c n)) →
    space.Random (fun seed => order.sup (fun n => c n seed) (hc seed))

variable {Ω : Type u} {source : Source Ω}

abbrev Hom (D E : Predomain source) :=
  {f : QuasiBorel.Hom D.space E.space // D.order.Continuous E.order f.toFun}

namespace Hom

variable {D E F : Predomain source}

instance : CoeFun (Hom D E) (fun _ => D.space.Carrier → E.space.Carrier) where
  coe := fun f => f.val.toFun

 theorem ext {f g : Hom D E} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (QuasiBorel.Hom.ext h)

@[expose] def identity (D : Predomain source) : Hom D D :=
  ⟨QuasiBorel.Hom.identity D.space, CPO.Continuous.identity D.order⟩

@[expose] def constant (D E : Predomain source) (x : E.space.Carrier) : Hom D E :=
  ⟨QuasiBorel.Hom.constant D.space E.space x, CPO.Continuous.constant D.order E.order x⟩

@[expose] def comp (g : Hom E F) (f : Hom D E) : Hom D F :=
  ⟨QuasiBorel.Hom.comp g.val f.val, g.property.comp f.property⟩

 theorem identity_left (f : Hom D E) : comp (identity E) f = f := ext (fun _ => rfl)
 theorem identity_right (f : Hom D E) : comp f (identity D) = f := ext (fun _ => rfl)
 theorem comp_assoc {G : Predomain source} (h : Hom F G) (g : Hom E F) (f : Hom D E) :
    comp (comp h g) f = comp h (comp g f) := ext (fun _ => rfl)

end Hom

namespace Predomain

@[expose] def discrete (space : Space source) : Predomain source where
  space := space
  order := CPO.discrete space.Carrier
  randomSup := fun _ _ hr => hr 0

@[expose] def discreteMap {D E : Space source} (f : QuasiBorel.Hom D E) :
    Hom (discrete D) (discrete E) :=
  ⟨f, CPO.continuous_from_discrete _ _⟩

 theorem discrete_full {D E : Space source} (f : Hom (discrete D) (discrete E)) :
    discreteMap f.val = f := Hom.ext (fun _ => rfl)

@[expose] def unrestricted (source : Source Ω) {α : Type v} (D : CPO α) : Predomain source where
  space := Space.unrestricted source α
  order := D
  randomSup := fun _ _ _ => True.intro

@[expose] def powerset (source : Source Ω) (α : Type v) : Predomain source :=
  unrestricted source (CPO.powerset α)

@[expose] def product (D E : Predomain source) : Predomain source where
  space := Space.product D.space E.space
  order := D.order.product E.order
  randomSup := fun c hc hr =>
    ⟨D.randomSup (fun n seed => (c n seed).1) (fun seed i j h => (hc seed i j h).1)
      (fun n => (hr n).1),
     E.randomSup (fun n seed => (c n seed).2) (fun seed i j h => (hc seed i j h).2)
      (fun n => (hr n).2)⟩

@[expose] def pi {ι : Type w} (D : ι → Predomain source) : Predomain source where
  space := Space.pi (fun i => (D i).space)
  order := CPO.pi (fun i => (D i).order)
  randomSup := fun c hc hr i => (D i).randomSup (fun n seed => c n seed i)
    (fun seed n m h => hc seed n m h i) (fun n => hr n i)

@[expose] def first (D E : Predomain source) : Hom (product D E) D :=
  ⟨Space.first D.space E.space, CPO.continuous_first _ _⟩

@[expose] def second (D E : Predomain source) : Hom (product D E) E :=
  ⟨Space.second D.space E.space, CPO.continuous_second _ _⟩

@[expose] def pair {D E F : Predomain source} (f : Hom D E) (g : Hom D F) :
    Hom D (product E F) := ⟨Space.pair f.val g.val, f.property.pair g.property⟩

 theorem first_pair {D E F : Predomain source} (f : Hom D E) (g : Hom D F) :
    Hom.comp (first E F) (pair f g) = f := Hom.ext (fun _ => rfl)

 theorem second_pair {D E F : Predomain source} (f : Hom D E) (g : Hom D F) :
    Hom.comp (second E F) (pair f g) = g := Hom.ext (fun _ => rfl)

 theorem pair_unique {D E F : Predomain source} (f : Hom D (product E F)) :
    pair (Hom.comp (first E F) f) (Hom.comp (second E F) f) = f := Hom.ext (fun _ => rfl)

@[expose] def terminal (source : Source Ω) : Predomain source :=
  discrete (Space.terminal source)

@[expose] def terminate (D : Predomain source) : Hom D (terminal source) :=
  Hom.constant D (terminal source) ()

 theorem terminate_unique (D : Predomain source) (f : Hom D (terminal source)) :
    f = terminate D := by
  apply Hom.ext
  intro x
  exact @Subsingleton.elim Unit _ (f x) ()

@[expose] def project {ι : Type w} (D : ι → Predomain source) (i : ι) :
    Hom (pi D) (D i) :=
  ⟨Space.project (fun i => (D i).space) i,
    ⟨fun h => h i, fun _ _ => rfl⟩⟩

@[expose] def tuple {ι : Type w} {D : Predomain source} {E : ι → Predomain source}
    (f : ∀ i, Hom D (E i)) : Hom D (pi E) :=
  ⟨Space.tuple (fun i => (f i).val),
    ⟨fun h i => (f i).property.monotone h,
     fun c hc => funext (fun i => (f i).property.preserves c hc)⟩⟩

 theorem project_tuple {ι : Type w} {D : Predomain source} {E : ι → Predomain source}
    (f : ∀ i, Hom D (E i)) (i : ι) : Hom.comp (project E i) (tuple f) = f i :=
  Hom.ext (fun _ => rfl)

 theorem tuple_unique {ι : Type w} {D : Predomain source} {E : ι → Predomain source}
    (f : Hom D (pi E)) : tuple (fun i => Hom.comp (project E i) f) = f :=
  Hom.ext (fun _ => rfl)

end Predomain

end

end Foundations.QuasiBorel.Domain
