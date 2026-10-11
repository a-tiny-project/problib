import Problib.QuasiBorel.Probability.Closed
import Problib.QuasiBorel.Subtype

set_option autoImplicit false

/-!
# Couplings of probability laws

A coupling of two laws under a relation is a joint law on the related pairs
whose marginals are the two laws. The joint law lives on the subspace of
related pairs, so the relation needs no measurability.

A coupling family is one morphism from a context to joint laws. A coupling at
each point of a context does not give a family, since a choice of joint law
at each point need not be a morphism. Families are closed under the monad's
unit and contextual bind, so sequenced programs get their couplings from
their parts.
-/

namespace Problib.QuasiBorel.Probability

open Problib.Measure.Real (borel)

variable {context left right left' right' pairs pairs' : Space (Source.ofMeasurable borel)}

/-- Contextual bind commutes with a projection of its laws: projecting the
bound law is binding the projected law against the projected kernel. -/
theorem map_bindContext (project : Hom pairs left) (project' : Hom pairs' left')
    {joint : Hom context (object pairs)} {laws : Hom context (object left)}
    {inner : Hom (Space.product context pairs) (object pairs')}
    {kernel : Hom (Space.product context left) (object left')}
    (outer : Hom.comp (map project) joint = laws)
    (step : Hom.comp (map project') inner =
      Hom.comp kernel (Space.productMap (Hom.identity context) project)) :
    Hom.comp (map project') (bindContext joint inner) = bindContext laws kernel := by
  apply Hom.ext
  intro point
  calc map project' (bindContext joint inner point)
      = bind (joint point) (Hom.comp (map project') (Space.curry inner point)) :=
        (congrArg (fun law => map project' law) (bindContext_apply joint inner point)).trans
          (map_bind project' _ _)
    _ = bind (joint point) (Hom.comp (Space.curry kernel point) project) :=
        congrArg (bind (joint point))
          (Hom.ext fun pair => congrArg (fun morphism => morphism (point, pair)) step)
    _ = bind (laws point) (Space.curry kernel point) :=
        (bind_map _ _ _).symm.trans
          (congrArg (fun law => bind law (Space.curry kernel point))
            (congrArg (fun morphism => morphism point) outer))
    _ = bindContext laws kernel point := (bindContext_apply laws kernel point).symm

/-- The related pairs, as a subspace of the product. -/
abbrev Pairs (related : left.Carrier → right.Carrier → Prop) : Space (Source.ofMeasurable borel) :=
  (Space.product left right).subtype (fun point => related point.1 point.2)

/-- The left point of a related pair. -/
def Pairs.first (related : left.Carrier → right.Carrier → Prop) : Hom (Pairs related) left :=
  Hom.comp (Space.first left right) (Space.subtypeVal _ _)

/-- The right point of a related pair. -/
def Pairs.second (related : left.Carrier → right.Carrier → Prop) : Hom (Pairs related) right :=
  Hom.comp (Space.second left right) (Space.subtypeVal _ _)

/-- Related pairs under a relation are related pairs under any weaker one. -/
def Pairs.weaken {related weaker : left.Carrier → right.Carrier → Prop}
    (weaken : ∀ leftPoint rightPoint, related leftPoint rightPoint → weaker leftPoint rightPoint) :
    Hom (Pairs related) (Pairs weaker) :=
  Hom.subtypeLift (Space.subtypeVal _ _) _ fun pair => weaken _ _ pair.property

/-- A point paired with itself. -/
def Pairs.diagonal : Hom left (Pairs (fun leftPoint rightPoint : left.Carrier => leftPoint = rightPoint)) :=
  Hom.subtypeLift (Space.pair (Hom.identity left) (Hom.identity left)) _ fun _ => rfl

/-- Some joint law on the related pairs has marginals `leftLaw` and `rightLaw`. -/
def Coupled (related : left.Carrier → right.Carrier → Prop) (leftLaw : Law left)
    (rightLaw : Law right) : Prop :=
  ∃ joint : Law (Pairs related),
    map (Pairs.first related) joint = leftLaw ∧ map (Pairs.second related) joint = rightLaw

/-- Dirac laws at related points are coupled. -/
theorem Coupled.pure {related : left.Carrier → right.Carrier → Prop} {leftPoint : left.Carrier}
    {rightPoint : right.Carrier} (holds : related leftPoint rightPoint) :
    Coupled related (Probability.pure left leftPoint) (Probability.pure right rightPoint) :=
  ⟨Probability.pure (Pairs related) ⟨(leftPoint, rightPoint), holds⟩,
    map_pure (Pairs.first related) _, map_pure (Pairs.second related) _⟩

/-- A coupling family over a context: one morphism to joint laws whose
marginals are the two families of laws. -/
structure Coupling (related : left.Carrier → right.Carrier → Prop)
    (leftLaws : Hom context (object left)) (rightLaws : Hom context (object right)) where
  joint : Hom context (object (Pairs related))
  first : Hom.comp (map (Pairs.first related)) joint = leftLaws
  second : Hom.comp (map (Pairs.second related)) joint = rightLaws

namespace Coupling

variable {related : left.Carrier → right.Carrier → Prop}
  {related' : left'.Carrier → right'.Carrier → Prop}
  {leftLaws : Hom context (object left)} {rightLaws : Hom context (object right)}

/-- A family couples its laws at every point. -/
theorem coupled (coupling : Coupling related leftLaws rightLaws) (point : context.Carrier) :
    Coupled related (leftLaws point) (rightLaws point) :=
  ⟨coupling.joint point, congrArg (fun morphism => morphism point) coupling.first,
    congrArg (fun morphism => morphism point) coupling.second⟩

/-- Restate a family's marginals along equalities. -/
noncomputable def congr {leftLaws' : Hom context (object left)} {rightLaws' : Hom context (object right)}
    (coupling : Coupling related leftLaws rightLaws) (leftSame : leftLaws = leftLaws')
    (rightSame : rightLaws = rightLaws') : Coupling related leftLaws' rightLaws' :=
  ⟨coupling.joint, coupling.first.trans leftSame, coupling.second.trans rightSame⟩

/-- A family over a context is a family over any context mapped into it. -/
noncomputable def comp {outside : Space (Source.ofMeasurable borel)}
    (coupling : Coupling related leftLaws rightLaws) (restrict : Hom outside context) :
    Coupling related (Hom.comp leftLaws restrict) (Hom.comp rightLaws restrict) where
  joint := Hom.comp coupling.joint restrict
  first := congrArg (fun morphism => Hom.comp morphism restrict) coupling.first
  second := congrArg (fun morphism => Hom.comp morphism restrict) coupling.second

/-- A family under a relation is a family under any weaker one. -/
noncomputable def mono {weaker : left.Carrier → right.Carrier → Prop}
    (weaken : ∀ leftPoint rightPoint, related leftPoint rightPoint → weaker leftPoint rightPoint)
    (coupling : Coupling related leftLaws rightLaws) : Coupling weaker leftLaws rightLaws where
  joint := Hom.comp (map (Pairs.weaken weaken)) coupling.joint
  first := Hom.ext fun point =>
    (congrArg (fun morphism => morphism (coupling.joint point))
      (map_comp (Pairs.first weaker) (Pairs.weaken weaken))).symm.trans
      (congrArg (fun morphism => morphism point) coupling.first)
  second := Hom.ext fun point =>
    (congrArg (fun morphism => morphism (coupling.joint point))
      (map_comp (Pairs.second weaker) (Pairs.weaken weaken))).symm.trans
      (congrArg (fun morphism => morphism point) coupling.second)

/-- The diagonal family couples a family of laws with itself under equality. -/
noncomputable def diagonal (laws : Hom context (object left)) :
    Coupling (fun leftPoint rightPoint : left.Carrier => leftPoint = rightPoint) laws laws where
  joint := Hom.comp (map Pairs.diagonal) laws
  first := Hom.ext fun point =>
    (congrArg (fun morphism => morphism (laws point)) (map_comp (Pairs.first _) Pairs.diagonal)).symm.trans
      (congrArg (fun morphism => morphism (laws point)) (map_id left))
  second := Hom.ext fun point =>
    (congrArg (fun morphism => morphism (laws point)) (map_comp (Pairs.second _) Pairs.diagonal)).symm.trans
      (congrArg (fun morphism => morphism (laws point)) (map_id left))

/-- Related deterministic families couple their Dirac laws. -/
noncomputable def pure (leftMap : Hom context left) (rightMap : Hom context right)
    (holds : ∀ point, related (leftMap point) (rightMap point)) :
    Coupling related (Hom.comp (unit left) leftMap) (Hom.comp (unit right) rightMap) where
  joint := Hom.comp (unit (Pairs related))
    (Hom.subtypeLift (Space.pair leftMap rightMap) _ holds)
  first := Hom.ext fun _ => map_pure (Pairs.first related) _
  second := Hom.ext fun _ => map_pure (Pairs.second related) _

/-- Contextual bind of coupled laws against a family that couples the two
kernels at every related pair carries the coupling through. The joint law is
the contextual bind of the joint laws, so no choice is made. -/
noncomputable def bind {leftKernel : Hom (Space.product context left) (object left')}
    {rightKernel : Hom (Space.product context right) (object right')}
    (outer : Coupling related leftLaws rightLaws)
    (inner : Coupling related'
      (Hom.comp leftKernel (Space.productMap (Hom.identity context) (Pairs.first related)))
      (Hom.comp rightKernel (Space.productMap (Hom.identity context) (Pairs.second related)))) :
    Coupling related' (bindContext leftLaws leftKernel) (bindContext rightLaws rightKernel) where
  joint := bindContext outer.joint inner.joint
  first := map_bindContext _ _ outer.first inner.first
  second := map_bindContext _ _ outer.second inner.second

/-- Related maps in context carry a coupling to a coupling of their images:
`bind` against the Dirac family. -/
noncomputable def map (outer : Coupling related leftLaws rightLaws)
    (leftMap : Hom (Space.product context left) left')
    (rightMap : Hom (Space.product context right) right')
    (holds : ∀ point (pair : (Pairs related).Carrier),
      related' (leftMap (point, pair.val.1)) (rightMap (point, pair.val.2))) :
    Coupling related' (bindContext leftLaws (Hom.comp (unit left') leftMap))
      (bindContext rightLaws (Hom.comp (unit right') rightMap)) :=
  outer.bind (Coupling.pure
    (Hom.comp leftMap (Space.productMap (Hom.identity context) (Pairs.first related)))
    (Hom.comp rightMap (Space.productMap (Hom.identity context) (Pairs.second related)))
    fun point => holds point.1 point.2)

end Coupling

end Problib.QuasiBorel.Probability
