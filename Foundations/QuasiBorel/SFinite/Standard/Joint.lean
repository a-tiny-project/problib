module

public import Foundations.QuasiBorel.SFinite.Standard.Family
public import Foundations.Measure.StandardBorel.Product
public import Foundations.Measure.Kernel.Product.Basic

set_option autoImplicit false

/-!
# Joint parameter-seed random families for s-finite quasi-Borel spaces

This module implements the Section 11 Definition 6 comparison with joint
parameter-seed standard-Borel generators.
Generators depend measurably on the product of parameter and standard seed.
Kernel attachment embeds joint families into shared families, demonstrating
equivalence with the fixed partial-real family predicate.
-/

namespace Foundations.QuasiBorel.SFinite.Standard

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v

/-- Parameterized random family with a joint generator from parameter and
standard-Borel seed space. -/
structure JointFamily (space : Space.{0, u} realSource) (laws : Carrier → Law space) where
  Seed : Type v
  source : Foundations.Measure.Space Seed
  standard : StandardBorel source
  random : Hom (Space.ofMeasurable borel (Foundations.Measure.Space.product borel source)) space
  kernel : Kernel borel source
  sfinite : Kernel.IsSFinite kernel
  law : ∀ seed, (kernel seed).map (fun point => random (seed, point))
    (MeasurableMap.comp
      (random.toMeasurable_ofEmbedding (StandardBorel.real.product standard).embeddingReal)
      (Kernel.pair_left_measurable seed)) = (laws seed).val

namespace JointFamily

variable {space : Space.{0, u} realSource} {laws : Carrier → Law space}

/-- Converts a joint parameter-seed family into a shared standard family via kernel attachment. -/
@[expose] noncomputable def toShared (family : JointFamily.{u, v} space laws) :
    Family.{u, v} space laws where
  Seed := Carrier × family.Seed
  source := Foundations.Measure.Space.product borel family.source
  standard := StandardBorel.real.product family.standard
  random := family.random
  kernel := family.kernel.attach family.sfinite
  sfinite := family.sfinite.attach
  law := by
    intro seed
    change ((family.kernel.attach family.sfinite) seed).map family.random _ = _
    rw [Kernel.attach_apply, Measure.map_comp]
    exact family.law seed

/-- Converts a shared standard family into a joint family by ignoring parameter in the generator. -/
@[expose] noncomputable def ofShared (family : Family.{u, v} space laws) :
    JointFamily.{u, v} space laws where
  Seed := family.Seed
  source := family.source
  standard := family.standard
  random := Hom.comp family.random
    (Hom.ofMeasurable (Foundations.Measure.Space.second_measurable borel family.source))
  kernel := family.kernel
  sfinite := family.sfinite
  law := fun seed => family.law seed

/-- Converts a joint parameter-seed family into a partial family from the real line. -/
@[expose] noncomputable def toPartial (family : JointFamily.{u, v} space laws) :
    SFinite.Family space laws :=
  family.toShared.toPartial

/-- Converts a partial family into a joint standard family with Type 0 source. -/
@[expose] noncomputable def ofPartial (family : SFinite.Family space laws) :
    JointFamily.{u, 0} space laws :=
  ofShared (Family.ofPartial family)

/-- Proves that a parameter family is random if and only if it admits a
joint parameter-seed standard-Borel family witness. -/
theorem random_iff (space : Space.{0, u} realSource) (laws : Carrier → Law space) :
    Random space laws ↔ Nonempty (JointFamily.{u, 0} space laws) := by
  constructor
  · rintro ⟨family⟩
    exact ⟨ofPartial family⟩
  · rintro ⟨family⟩
    exact ⟨family.toPartial⟩

end JointFamily

end

end Foundations.QuasiBorel.SFinite.Standard
