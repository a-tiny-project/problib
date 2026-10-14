module

public import Problib.QuasiBorel.SFinite.Monad

/-!
# Countable sums of s-finite quasi-Borel laws and counting laws

This module sums countably many s-finite laws on one quasi-Borel space. The sum
of their presentations joins the summands' generators over a measurable
partition of the real line and sums their source measures, each moved into its
own piece. A law-valued morphism sums pointwise, so countable sums of
quasi-Borel morphisms into the law space are morphisms too. A counting law
puts unit mass on each point a decoding of the naturals names, and binding
against it sums the continuation over those points.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u

variable {space : Space realSource}

/-- Sums countably many presentations: each summand's generator runs on its own
piece of the real line, which carries that summand's source measure. -/
@[expose] noncomputable def Presentation.sum (presentations : Nat → Presentation space) :
    Presentation space where
  random := RandomFamily.join (fun index => (presentations index).random)
  accepted := RandomFamily.join_random (fun index => (presentations index).accepted)
  sourceMeasure := Measure.sum (fun index => (presentations index).sourceMeasure.map
    (RandomFamily.select index) (RandomFamily.select_measurable index))
  sfinite := Measure.SFinite.sum _ (fun index => (presentations index).sfinite.map
    (RandomFamily.select index) (RandomFamily.select_measurable index))

/-- The summed presentation interprets as the sum of the summands' measures. -/
theorem Presentation.sum_toMeasure (presentations : Nat → Presentation space) :
    (Presentation.sum presentations).toMeasure =
      Measure.sum (fun index => (presentations index).toMeasure) := by
  change ((Measure.sum _).map (Presentation.sum presentations).random
    (Space.random_measurable (Presentation.sum presentations).accepted)).comap _ = _
  rw [Measure.map_sum, Measure.comap_sum]
  apply congrArg Measure.sum
  funext index
  rw [Measure.map_comp _ _ _ (RandomFamily.select_measurable index)
    (Space.random_measurable (Presentation.sum presentations).accepted)]
  have equal : (fun seed => (Presentation.sum presentations).random
      (RandomFamily.select index seed)) = (presentations index).random :=
    funext (RandomFamily.join_select _ index)
  simp only [equal]
  rfl

/-- The countable sum of represented laws. -/
@[expose] noncomputable def Law.sum (laws : Nat → Law space) : Law space :=
  ⟨Measure.sum (fun index => (laws index).val),
    Presentation.sum (fun index => (laws index).presentation), by
      rw [Presentation.sum_toMeasure]
      exact congrArg Measure.sum (funext fun index => (laws index).presentation_toMeasure)⟩

/-- The summed law's measure is the sum of the summands' measures. -/
@[simp] theorem Law.sum_val (laws : Nat → Law space) :
    (Law.sum laws).val = Measure.sum (fun index => (laws index).val) := rfl

/-- Sums countably many families of laws with one shared generator and the
summed kernel. -/
@[expose] noncomputable def Family.sum {laws : Nat → Carrier → Law space}
    (families : ∀ index, Family space (laws index)) :
    Family space (fun seed => Law.sum (fun index => laws index seed)) where
  random := RandomFamily.join (fun index => (families index).random)
  accepted := RandomFamily.join_random (fun index => (families index).accepted)
  kernel := Kernel.sum (fun index => (families index).kernel.map
    (RandomFamily.select index) (RandomFamily.select_measurable index))
  sfinite := Kernel.IsSFinite.sum _ (fun index => (families index).sfinite.map
    (RandomFamily.select index) (RandomFamily.select_measurable index))
  law := by
    intro seed
    change (Measure.sum (fun index => ((families index).kernel seed).map
      (RandomFamily.select index) (RandomFamily.select_measurable index)) |>.map
        (RandomFamily.join (fun index => (families index).random))
        (Space.random_measurable
          (RandomFamily.join_random (fun index => (families index).accepted)))).comap _ = _
    rw [Measure.map_sum, Measure.comap_sum]
    apply congrArg Measure.sum
    funext index
    rw [Measure.map_comp]
    have equal : (fun point => RandomFamily.join (fun index => (families index).random)
        (RandomFamily.select index point)) = (families index).random :=
      funext (RandomFamily.join_select _ index)
    simp only [equal]
    exact (families index).law seed

variable {domain : Space realSource}

/-- The pointwise countable sum of law-valued quasi-Borel morphisms. -/
@[expose] noncomputable def sum (kernels : Nat → Hom domain (object space)) :
    Hom domain (object space) where
  toFun := fun point => Law.sum (fun index => kernels index point)
  map_random := by
    intro random accepted
    exact ⟨Family.sum (fun index => Classical.choice ((kernels index).map_random accepted))⟩

/-- The summed morphism sums its summands' laws at each point. -/
@[simp] theorem sum_apply (kernels : Nat → Hom domain (object space)) (point : domain.Carrier) :
    sum kernels point = Law.sum (fun index => kernels index point) := rfl

/-- Two sums agree at two points when their summands agree there. -/
theorem sum_congr_at {other : Space realSource} (left : Nat → Hom domain (object space))
    (right : Nat → Hom other (object space)) {leftPoint : domain.Carrier}
    {rightPoint : other.Carrier}
    (equal : ∀ index, left index leftPoint = right index rightPoint) :
    sum left leftPoint = sum right rightPoint := by
  apply Law.ext
  exact congrArg Measure.sum (funext fun index => congrArg Subtype.val (equal index))

/-- Pushforward commutes with countable sums of laws. -/
theorem map_sum {codomain : Space realSource} (function : Hom space codomain)
    (laws : Nat → Law space) :
    map function (Law.sum laws) = Law.sum (fun index => map function (laws index)) := by
  apply Law.ext
  rw [map_val, Law.sum_val, Law.sum_val, Measure.map_sum]
  exact congrArg Measure.sum (funext fun index => (map_val function (laws index)).symm)

/-- The term a decoded natural contributes: the Dirac law at its point, or the
zero law where the decoding names no point. -/
@[expose] noncomputable def countingTerm (space : Space realSource)
    (decode : Nat → Option space.Carrier) (index : Nat) : Law space :=
  match decode index with
  | some point => pure space point
  | none => zero space

/-- The counting law of a decoding: unit mass at each point a natural decodes to. -/
@[expose] noncomputable def counting (space : Space realSource)
    (decode : Nat → Option space.Carrier) : Law space :=
  Law.sum (countingTerm space decode)

/-- Binding against a counting law sums the continuation over the decoded points. -/
theorem bind_counting {codomain : Space realSource} (decode : Nat → Option space.Carrier)
    (kernel : Hom space (object codomain)) :
    bind (counting space decode) kernel =
      Law.sum (fun index => match decode index with
        | some point => kernel point
        | none => zero codomain) := by
  apply Law.ext
  rw [bind_val, counting, Law.sum_val, Law.sum_val, Measure.bind_sum_left]
  apply congrArg Measure.sum
  funext index
  unfold countingTerm
  cases decode index with
  | some point => exact Measure.dirac_bind point (toKernel kernel)
  | none => exact Measure.zero_bind (toKernel kernel)

end

end Problib.QuasiBorel.SFinite
