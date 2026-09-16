import Foundations.Measure.Giry.Kernel
import Foundations.Measure.Kernel.Composition
import Foundations.Measure.Kernel.Composition.Bind.Transport

set_option autoImplicit false

namespace Foundations.Measure.Giry

open Foundations.Real

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {source : Space α} {target : Space β} {result : Space γ}

/-- Dirac probability law at a given point on a measurable space. -/
noncomputable def pure (source : Space α) (point : α) : Law source :=
  ⟨Measure.dirac source point, Measure.IsProbability.dirac source point⟩

/-- The Dirac unit is a measurable map from `source` into `space source`. -/
theorem pure_measurable (source : Space α) :
    MeasurableMap source (space source) (pure source) := by
  apply (measurable_iff _).mpr
  exact (Kernel.deterministic (fun point : α => point)
    (MeasurableMap.identity source)).measurable

/-- Pushforward (functorial map) of a probability law along a measurable
function. -/
noncomputable def map (function : α → β)
    (measurable : MeasurableMap source target function)
    (law : Law source) : Law target :=
  ⟨law.val.map function measurable, law.property.map function measurable⟩

/-- Functorial map on probability laws is measurable between law spaces. -/
theorem map_measurable (function : α → β)
    (measurable : MeasurableMap source target function) :
    MeasurableMap (space source) (space target) (map function measurable) := by
  apply (measurable_iff _).mpr
  exact ((evaluationKernel source).map function measurable).measurable

/-- Monadic bind of a probability law along a measurable continuation into
`space target`. -/
noncomputable def bind (law : Law source) (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) : Law target :=
  ⟨law.val.bind (toKernel family measurable),
    law.property.bind _ (fun input => (family input).property)⟩

/-- Monadic bind is measurable with respect to the input law for a fixed
measurable continuation. -/
theorem bind_measurable (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    MeasurableMap (space source) (space target)
      (fun law => bind law family measurable) := by
  apply (measurable_iff _).mpr
  exact ((evaluationKernel source).comp (toKernel family measurable)).measurable

/-- Left Kleisli unit: binding a Dirac point law against a continuation returns
the continuation evaluated at that point. -/
theorem pure_bind (point : α) (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    bind (pure source point) family measurable = family point := by
  apply Subtype.ext
  exact Measure.dirac_bind point (toKernel family measurable)

/-- Right Kleisli unit: binding a probability law against the Dirac unit
recovers the original law. -/
theorem bind_pure (law : Law source) :
    bind law (pure source) (pure_measurable source) = law := by
  apply Subtype.ext
  change law.val.bind (Kernel.deterministic (fun point : α => point)
    (MeasurableMap.identity source)) = law.val
  rw [Measure.bind_deterministic, Measure.map_id]

/-- Associativity of monadic bind for measurable continuations. -/
theorem bind_assoc (law : Law source) (first : α → Law target)
    (firstMeasurable : MeasurableMap source (space target) first)
    (second : β → Law result)
    (secondMeasurable : MeasurableMap target (space result) second) :
    bind (bind law first firstMeasurable) second secondMeasurable =
      bind law (fun input => bind (first input) second secondMeasurable)
        (MeasurableMap.comp (bind_measurable second secondMeasurable)
          firstMeasurable) := by
  apply Subtype.ext
  exact Measure.bind_assoc law.val (toKernel first firstMeasurable)
    (toKernel second secondMeasurable)

/-- Monadic join: flattening a probability law of laws into a single law. -/
noncomputable def join (law : Law (space source)) : Law source :=
  bind law (fun value => value) (MeasurableMap.identity (space source))

/-- Monadic join is a measurable map from `space (space source)` to
`space source`. -/
theorem join_measurable : MeasurableMap (space (space source))
    (space source) join :=
  bind_measurable (fun value => value) (MeasurableMap.identity (space source))

/-- Inhabitation: a probability law space is nonempty if and only if the
underlying carrier space is nonempty, handling empty carriers honestly. -/
theorem nonempty_iff (source : Space α) : Nonempty (Law source) ↔ Nonempty α := by
  constructor
  · rintro ⟨law⟩
    exact law.property.nonempty
  · rintro ⟨point⟩
    exact ⟨pure source point⟩

/-- Functor identity law for pushforward of probability laws. -/
theorem map_id (law : Law source) :
    map (fun value => value) (MeasurableMap.identity source) law = law :=
  Subtype.ext (Measure.map_id law.val)

/-- Functor composition law for pushforward of probability laws. -/
theorem map_comp (law : Law source) (before : α → β) (after : β → γ)
    (beforeMeasurable : MeasurableMap source target before)
    (afterMeasurable : MeasurableMap target result after) :
    map after afterMeasurable (map before beforeMeasurable law) =
      map (fun value => after (before value))
        (MeasurableMap.comp afterMeasurable beforeMeasurable) law :=
  Subtype.ext (Measure.map_comp law.val before after beforeMeasurable afterMeasurable)

/-- Functorial map preserves the Dirac unit. -/
theorem map_pure (function : α → β)
    (measurable : MeasurableMap source target function) (point : α) :
    map function measurable (pure source point) = pure target (function point) :=
  Subtype.ext (Measure.map_dirac function measurable point)

/-- Evaluating a bound law on a measurable region equals the lower Lebesgue
integral of the continuation evaluations. -/
theorem bind_apply (law : Law source) (family : α → Law target)
    (measurable : MeasurableMap source (space target) family)
    {region : Set β} (regionMeasurable : target.Measurable region) :
    (bind law family measurable).val region =
      lintegral law.val (fun input => (family input).val region) :=
  Measure.bind_apply law.val (toKernel family measurable) regionMeasurable

/-- Iterated integration against a bound law equals nested lower Lebesgue
integrals. -/
theorem lintegral_bind (law : Law source) (family : α → Law target)
    (measurable : MeasurableMap source (space target) family)
    {function : β → ENNReal} (functionMeasurable : ENNRealMeasurable target function) :
    lintegral (bind law family measurable).val function =
      lintegral law.val (fun input => lintegral (family input).val function) :=
  Measure.lintegral_bind law.val (toKernel family measurable) functionMeasurable

/-- Lower Lebesgue integration against a fixed measurable ENNReal function is
measurable across laws. -/
theorem lintegral_measurable {function : α → ENNReal}
    (measurable : ENNRealMeasurable source function) :
    ENNRealMeasurable (space source) (fun law => lintegral law.val function) :=
  (evaluationKernel source).lintegral_measurable measurable

/-- Binding against a constant law family produces that constant law, with
total mass one discharging the scaling factor. -/
theorem bind_const (law : Law source) (other : Law target) :
    bind law (fun _ => other) (MeasurableMap.constant source (space target) other) =
      other := by
  apply Subtype.ext
  change law.val.bind (Kernel.const source other.val) = other.val
  rw [Measure.bind_const, law.property.univ_eq_one, Measure.one_smul]

/-- Binding against a deterministic map composed with pure equals functorial
pushforward map. -/
theorem bind_pure_comp (law : Law source) (function : α → β)
    (measurable : MeasurableMap source target function) :
    bind law (fun point => pure target (function point))
      (MeasurableMap.comp (pure_measurable target) measurable) =
      map function measurable law := by
  apply Subtype.ext
  exact Measure.bind_deterministic law.val function measurable

/-- Binding a pushed-forward law along a measurable map equals binding the
original law with continuation precomposition. -/
theorem bind_map (law : Law source) (function : α → β)
    (functionMeasurable : MeasurableMap source target function)
    (family : β → Law result)
    (familyMeasurable : MeasurableMap target (space result) family) :
    bind (map function functionMeasurable law) family familyMeasurable =
      bind law (fun point => family (function point))
        (MeasurableMap.comp familyMeasurable functionMeasurable) := by
  apply Subtype.ext
  exact Measure.bind_map law.val function functionMeasurable (toKernel family familyMeasurable)

/-- Pushing forward a bound law along a measurable function commutes with
continuation postcomposition. -/
theorem map_bind (law : Law source) (family : α → Law target)
    (familyMeasurable : MeasurableMap source (space target) family)
    (function : β → γ) (functionMeasurable : MeasurableMap target result function) :
    map function functionMeasurable (bind law family familyMeasurable) =
      bind law (fun point => map function functionMeasurable (family point))
        (MeasurableMap.comp (map_measurable function functionMeasurable) familyMeasurable) := by
  apply Subtype.ext
  exact Measure.map_bind law.val (toKernel family familyMeasurable) function functionMeasurable

/-- The kernel associated with the Dirac unit is the deterministic identity
kernel. -/
theorem toKernel_pure (source : Space α) :
    toKernel (pure source) (pure_measurable source) =
      Kernel.deterministic (fun value : α => value) (MeasurableMap.identity source) := by
  apply Kernel.ext
  intro input
  rfl

/-- Giry monadic bind preserves probability kernel composition. -/
theorem toKernel_bind (first : α → Law target)
    (firstMeasurable : MeasurableMap source (space target) first)
    (second : β → Law result)
    (secondMeasurable : MeasurableMap target (space result) second) :
    toKernel (fun input => bind (first input) second secondMeasurable)
      (MeasurableMap.comp (bind_measurable second secondMeasurable) firstMeasurable) =
      (toKernel first firstMeasurable).comp (toKernel second secondMeasurable) := by
  apply Kernel.ext
  intro input
  rfl

/-- Monadic bind expressed through join and functorial map. -/
theorem bind_eq_join_map (law : Law source) (family : α → Law target)
    (measurable : MeasurableMap source (space target) family) :
    bind law family measurable = join (map family measurable law) :=
  (bind_map law family measurable (fun value => value)
    (MeasurableMap.identity (space target))).symm

/-- Monadic join on a Dirac unit law is the identity. -/
theorem join_pure (law : Law source) : join (pure (space source) law) = law :=
  pure_bind law (fun value => value) (MeasurableMap.identity (space source))

/-- Monadic join on pushed-forward Dirac laws is the identity. -/
theorem join_map_pure (law : Law source) :
    join (map (pure source) (pure_measurable source) law) = law := by
  unfold join
  rw [bind_map law (pure source) (pure_measurable source) (fun value => value)
    (MeasurableMap.identity (space source))]
  exact bind_pure law

/-- Associativity coherence for monadic join. -/
theorem join_assoc (law : Law (space (space source))) :
    join (join law) = join (map join join_measurable law) := by
  unfold join
  rw [bind_assoc, bind_map] <;> exact MeasurableMap.identity _

/-- Naturality of monadic join with respect to pushforward map. -/
theorem join_map (law : Law (space source)) (function : α → β)
    (measurable : MeasurableMap source target function) :
    map function measurable (join law) =
      join (map (map function measurable) (map_measurable function measurable) law) := by
  unfold join
  rw [map_bind, bind_map] <;> exact MeasurableMap.identity _

end Foundations.Measure.Giry
