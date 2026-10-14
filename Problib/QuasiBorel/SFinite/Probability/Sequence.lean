import Problib.QuasiBorel.SFinite.Probability.Product
import Problib.QuasiBorel.SFinite.Sequence

/-!
# Finite independent products of probability laws

The independent product of two probability laws is their s-finite product,
which has mass one, read back as a probability law through the isomorphism of
probability laws with mass-one s-finite laws. Finitely many law-valued
morphisms of one parameter then multiply by the same recursion as their
s-finite twins, and the inclusion into s-finite laws carries each product to the
s-finite product of the included factors.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space

variable {domain space left right : Space SFinite.realSource}

/-- The independent product of two probability laws: their s-finite product,
restricted to mass one. -/
noncomputable def product (left right : Space SFinite.realSource) :
    Hom (Space.product (object left) (object right)) (object (Space.product left right)) :=
  Hom.comp (SFinite.Normalized.toProbabilityHom _)
    ((Hom.comp (SFinite.product left right)
      (Space.productMap (SFinite.ofProbabilityHom left)
        (SFinite.ofProbabilityHom right))).subtypeLift
      _ fun point => SFinite.product_probability _ _
        (SFinite.ofProbability_probability point.1) (SFinite.ofProbability_probability point.2))

/-- Included into s-finite laws, the product of two probability laws is the
s-finite product of the included laws. -/
theorem ofProbability_product (first : Law left) (second : Law right) :
    SFinite.ofProbability (product left right (first, second)) =
      SFinite.product left right (SFinite.ofProbability first, SFinite.ofProbability second) := by
  apply SFinite.Law.ext
  rfl

/-- Sample two law-valued morphisms of one parameter independently and keep
both results. -/
noncomputable def pair (first : Hom domain (object left)) (second : Hom domain (object right)) :
    Hom domain (object (Space.product left right)) :=
  Hom.comp (product left right) (Space.pair first second)

/-- Sample `count` law-valued morphisms of one parameter independently and
collect their results into a tuple. -/
noncomputable def sequence :
    (count : Nat) → (Fin count → Hom domain (object space)) →
      Hom domain (object (Space.pi fun _ : Fin count => space))
  | 0, _ => Hom.comp (unit _) (Hom.constant _ _ fun index => index.elim0)
  | count + 1, family =>
      Hom.comp (map (SFinite.cons space count))
        (pair (family 0) (sequence count fun index => family index.succ))

/-- Included into s-finite laws, the product of probability laws is the
s-finite product of the included factors. -/
theorem ofProbability_sequence :
    (count : Nat) → (family : Fin count → Hom domain (object space)) →
      (point : domain.Carrier) →
      SFinite.ofProbability (sequence count family point) =
        SFinite.sequence count
          (fun index => Hom.comp (SFinite.ofProbabilityHom space) (family index)) point
  | 0, _, _ =>
      congrArg (fun morphism : Hom (Space.pi fun _ : Fin 0 => space)
          (SFinite.object (Space.pi fun _ : Fin 0 => space)) =>
        morphism.toFun fun index => index.elim0)
        (SFinite.of_probability_unit (Space.pi fun _ : Fin 0 => space))
  | count + 1, family, point => by
      change SFinite.ofProbability (map (SFinite.cons space count)
          (product space (Space.pi fun _ : Fin count => space)
            (family 0 point, sequence count (fun index => family index.succ) point))) =
        SFinite.map (SFinite.cons space count)
          (SFinite.product space (Space.pi fun _ : Fin count => space)
            (SFinite.ofProbability (family 0 point),
              SFinite.sequence count (fun index => Hom.comp (SFinite.ofProbabilityHom space)
                (family index.succ)) point))
      rw [SFinite.ofProbability_map, ofProbability_product, ofProbability_sequence count]

/-- Two products agree at two parameters when their factors agree there. -/
theorem sequence_congr_at {other : Space SFinite.realSource} (count : Nat)
    (left : Fin count → Hom domain (object space))
    (right : Fin count → Hom other (object space))
    {leftPoint : domain.Carrier} {rightPoint : other.Carrier}
    (equal : ∀ index, left index leftPoint = right index rightPoint) :
    sequence count left leftPoint = sequence count right rightPoint := by
  apply SFinite.ofProbability_injective
  rw [ofProbability_sequence, ofProbability_sequence]
  exact SFinite.sequence_congr_at count _ _ fun index =>
    congrArg SFinite.ofProbability (equal index)

end Problib.QuasiBorel.Probability
