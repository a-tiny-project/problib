module

public import Foundations.QuasiBorel.SFinite.Standard.Presentation
public import Foundations.QuasiBorel.SFinite.Random

set_option autoImplicit false

/-!
# Standard-Borel random families of s-finite laws

This module defines parameterized random families of s-finite laws sharing a
total standard-Borel generator and a global s-finite kernel.
It establishes bidirectional conversions with partial-real families and proves
that standard-Borel family witnesses characterize the random law predicate.
-/

namespace Foundations.QuasiBorel.SFinite.Standard

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v

/-- Parameterized family of laws sharing a standard-Borel generator and a
globally s-finite transition kernel. -/
structure Family (space : Space.{0, u} realSource) (laws : Carrier → Law space)
    extends Generator.{u, v} space where
  kernel : Kernel borel source
  sfinite : Kernel.IsSFinite kernel
  law : ∀ seed, (kernel seed).map random toGenerator.measurable = (laws seed).val

namespace Family

variable {space : Space.{0, u} realSource} {laws : Carrier → Law space}

/-- Converts a standard-Borel family into a partial family from the real line. -/
@[expose] noncomputable def toPartial (family : Family.{u, v} space laws) :
    SFinite.Family space laws where
  toGenerator := family.toGenerator.toPartial
  kernel := family.kernel.map family.standard.embeddingReal.function
    family.standard.embeddingReal.measurable
  sfinite := family.sfinite.map family.standard.embeddingReal.function
    family.standard.embeddingReal.measurable
  law := fun seed => (family.toGenerator.toPartial_map (family.kernel seed)).trans (family.law seed)

/-- Converts a partial family into a standard-Borel family with Type 0 source. -/
@[expose] noncomputable def ofPartial (family : SFinite.Family space laws) :
    Family.{u, 0} space laws where
  toGenerator := Generator.ofPartial family.toGenerator
  kernel := family.kernel.comap family.toGenerator.seedEmbedding
  sfinite := family.sfinite.comap family.toGenerator.seedEmbedding
  law := fun seed => (family.toGenerator.map_comap_decode (family.kernel seed)).trans (family.law seed)

/-- Proves that a parameter family is random if and only if it admits a
standard-Borel family witness. -/
theorem random_iff (space : Space.{0, u} realSource) (laws : Carrier → Law space) :
    Random space laws ↔ Nonempty (Family.{u, 0} space laws) := by
  constructor
  · rintro ⟨family⟩
    exact ⟨ofPartial family⟩
  · rintro ⟨family⟩
    exact ⟨family.toPartial⟩

end Family

end

end Foundations.QuasiBorel.SFinite.Standard
