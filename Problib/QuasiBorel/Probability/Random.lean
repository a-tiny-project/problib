import Problib.QuasiBorel.Measurable.Family
import Problib.QuasiBorel.Probability.Representation

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v

/-- Proof-relevant representation data for a family of probability laws parameterized by real seeds, sharing a single accepted random element and a measurable probability kernel. -/
structure Family (space : Space (Source.ofMeasurable borel)) (laws : Carrier → Law space) where
  random : Carrier → space.Carrier
  accepted : space.Random random
  kernel : Carrier → Giry.Law borel
  measurable : MeasurableMap borel (Giry.space borel) kernel
  law : ∀ seed, Giry.map random (Space.random_measurable accepted) (kernel seed) = (laws seed).val

/-- Acceptance predicate for random elements into the probability space, defined by the existence of a representing family. -/
def Random (space : Space (Source.ofMeasurable borel)) (laws : Carrier → Law space) : Prop :=
  Nonempty (Family space laws)

namespace Family

variable {space : Space (Source.ofMeasurable borel)}

/-- Packages a constant family of laws using the law's chosen presentation. -/
noncomputable def constant (law : Law space) : Family space (fun _ => law) where
  random := law.presentation.random
  accepted := law.presentation.accepted
  kernel := fun _ => law.presentation.sourceLaw
  measurable := MeasurableMap.constant borel (Giry.space borel) law.presentation.sourceLaw
  law := fun _ => law.presentation_toGiry

/-- Precomposition with a measurable real map preserves the family representation by composing the kernel. -/
def reparam {laws : Carrier → Law space} (family : Family space laws)
    {parameter : Carrier → Carrier} (measurable : MeasurableMap borel borel parameter) :
    Family space (fun seed => laws (parameter seed)) where
  random := family.random
  accepted := family.accepted
  kernel := fun seed => family.kernel (parameter seed)
  measurable := MeasurableMap.comp family.measurable measurable
  law := fun seed => family.law (parameter seed)

/-- Countable piecewise combination of families across a measurable partition using joined random elements and selected kernels. -/
noncomputable def piecewise {partition : Carrier → Nat}
    (partitionMeasurable : (Source.ofMeasurable borel).Partition partition)
    {branches : Nat → Carrier → Law space} (families : ∀ index, Family space (branches index)) :
    Family space (fun seed => branches (partition seed) seed) where
  random := RandomFamily.join (fun index => (families index).random)
  accepted := RandomFamily.join_random (fun index => (families index).accepted)
  kernel := fun seed => Giry.map (RandomFamily.select (partition seed))
    (RandomFamily.select_measurable (partition seed)) ((families (partition seed)).kernel seed)
  measurable := MeasurableMap.countable_piecewise partitionMeasurable
    (fun index => MeasurableMap.comp
      (Giry.map_measurable (RandomFamily.select index) (RandomFamily.select_measurable index))
      (families index).measurable)
  law := by
    intro seed
    rw [Giry.map_comp]
    have equal :
        (fun point => RandomFamily.join (fun index => (families index).random)
          (RandomFamily.select (partition seed) point)) = (families (partition seed)).random :=
      funext (RandomFamily.join_select _ (partition seed))
    simpa only [equal] using (families (partition seed)).law seed

end Family

/-- The probability quasi-Borel space on representable laws over an arbitrary quasi-Borel space. -/
noncomputable def object (space : Space (Source.ofMeasurable borel)) :
    Space (Source.ofMeasurable borel) where
  Carrier := Law space
  Random := Random space
  constant := fun law => ⟨Family.constant law⟩
  reparam := by
    intro parameter random measurable accepted
    exact ⟨(Classical.choice accepted).reparam measurable⟩
  piecewise := by
    intro partition branches measurable accepted
    exact ⟨Family.piecewise measurable (fun index => Classical.choice (accepted index))⟩

/-- The inclusion of representable laws into Giry probability laws is measurable between the induced spaces. -/
theorem toGiry_measurable (space : Space (Source.ofMeasurable borel)) :
    MeasurableMap (object space).toMeasurable (Giry.space space.toMeasurable)
      (fun law : Law space => law.val) := by
  apply Space.measurableMap_iff_random.mpr
  intro random accepted
  rcases accepted with ⟨family⟩
  have equal : (fun seed => (random seed).val) =
      (fun seed => Giry.map family.random (Space.random_measurable family.accepted)
        (family.kernel seed)) := funext (fun seed => (family.law seed).symm)
  rw [equal]
  intro region measurable
  exact family.measurable
    (Giry.map_measurable family.random (Space.random_measurable family.accepted) measurable)

/-- The inclusion of representable laws into Giry probability laws is injective. -/
theorem toGiry_injective (space : Space (Source.ofMeasurable borel)) :
    Function.Injective (fun law : Law space => law.val) :=
  fun _ _ equal => Law.ext equal

end Problib.QuasiBorel.Probability
