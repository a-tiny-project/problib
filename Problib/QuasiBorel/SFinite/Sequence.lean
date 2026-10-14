module

public import Problib.QuasiBorel.SFinite.Product
public import Problib.QuasiBorel.Pi

/-!
# Finite independent products of s-finite quasi-Borel laws

This module samples finitely many law-valued morphisms of one parameter
independently and collects their results into a tuple indexed by `Fin n`. The
product of no laws is the Dirac law at the empty tuple, and the product of
`n + 1` laws pairs the first law with the product of the rest and conses the
pair into a tuple, so each step is the binary product `SFinite.product`.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space

variable {domain space : Space realSource}

/-- Cons a head onto a tuple indexed by `Fin n`. -/
@[expose] def cons (space : Space realSource) (count : Nat) :
    Hom (Space.product space (Space.pi fun _ : Fin count => space))
      (Space.pi fun _ : Fin (count + 1) => space) where
  toFun := fun pair => Fin.cases pair.1 pair.2
  map_random := by
    intro random accepted index
    refine Fin.cases ?_ (fun index => ?_) index
    · exact accepted.1
    · exact accepted.2 index

/-- Sample two law-valued morphisms of one parameter independently and keep
both results. -/
@[expose] noncomputable def pair {left right : Space realSource}
    (first : Hom domain (object left)) (second : Hom domain (object right)) :
    Hom domain (object (Space.product left right)) :=
  Hom.comp (product left right) (Space.pair first second)

/-- At a parameter, the pair is the product of the two laws there. -/
theorem pair_apply {left right : Space realSource} (first : Hom domain (object left))
    (second : Hom domain (object right)) (point : domain.Carrier) :
    pair first second point = product left right (first point, second point) :=
  rfl

/-- Sample `count` law-valued morphisms of one parameter independently and
collect their results into a tuple. -/
@[expose] noncomputable def sequence :
    (count : Nat) → (Fin count → Hom domain (object space)) →
      Hom domain (object (Space.pi fun _ : Fin count => space))
  | 0, _ => Hom.comp (unit _) (Hom.constant _ _ fun index => index.elim0)
  | count + 1, family =>
      Hom.comp (map (cons space count))
        (pair (family 0) (sequence count fun index => family index.succ))

/-- The product of no laws is the Dirac law at the empty tuple. -/
theorem sequence_zero (family : Fin 0 → Hom domain (object space)) (point : domain.Carrier) :
    sequence 0 family point = pure _ fun index => index.elim0 :=
  rfl

/-- The product of `count + 1` laws conses the first law's result onto the
product of the rest, sampled independently. -/
theorem sequence_succ (count : Nat) (family : Fin (count + 1) → Hom domain (object space))
    (point : domain.Carrier) :
    sequence (count + 1) family point =
      map (cons space count)
        (product space (Space.pi fun _ : Fin count => space)
          (family 0 point, sequence count (fun index => family index.succ) point)) :=
  rfl

/-- Two products agree at two parameters when their factors agree there. -/
theorem sequence_congr_at {other : Space realSource} :
    (count : Nat) → (left : Fin count → Hom domain (object space)) →
      (right : Fin count → Hom other (object space)) →
      {leftPoint : domain.Carrier} → {rightPoint : other.Carrier} →
      (∀ index, left index leftPoint = right index rightPoint) →
      sequence count left leftPoint = sequence count right rightPoint
  | 0, _, _, _, _, _ => rfl
  | count + 1, left, right, leftPoint, rightPoint, equal => by
      rw [sequence_succ, sequence_succ, equal 0,
        sequence_congr_at count (fun index => left index.succ) (fun index => right index.succ)
          fun index => equal index.succ]

end

end Problib.QuasiBorel.SFinite
