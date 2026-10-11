import Problib.Measure.Giry.Monad
import Problib.Measure.Giry.StandardBorel

set_option autoImplicit false

namespace Problib.Measure.Giry.Necessity

open Problib.Real

/-- A family of Dirac point laws on discrete `Bool`, indexed by `Bool`. -/
noncomputable def pointLaws : Bool → Law (Space.discrete Bool) :=
  pure (Space.discrete Bool)

/-- The family of point laws is not measurable when the domain `Bool` is
equipped with the indiscrete sigma-algebra. -/
theorem pointLaws_not_measurable :
    ¬MeasurableMap (Space.indiscrete Bool) (space (Space.discrete Bool)) pointLaws := by
  intro measurable
  have accepted := ((measurable_iff pointLaws).mp measurable
    (region := fun value => value = true) True.intro) ENNReal.zero
  have trueMember : ENNReal.lt ENNReal.zero ((pointLaws true).val (fun value => value = true)) := by
    change ENNReal.lt ENNReal.zero ((Measure.dirac (Space.discrete Bool) true) _)
    rw [Measure.dirac_apply_of_mem (Space.discrete Bool) true
      (set := fun value => value = true) True.intro rfl]
    exact ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero
  have falseAbsent : ¬ENNReal.lt ENNReal.zero ((pointLaws false).val (fun value => value = true)) := by
    change ¬ENNReal.lt ENNReal.zero ((Measure.dirac (Space.discrete Bool) false) _)
    rw [Measure.dirac_apply_of_not_mem (Space.discrete Bool) false
      (set := fun value => value = true) True.intro Bool.false_ne_true]
    exact fun positive => ENNReal.zero_lt_iff_ne_zero.mp positive rfl
  rcases (Space.indiscrete_measurable_iff _).mp accepted with empty | whole
  · have absent := congrArg (fun region => region true) empty
    exact absent.mp trueMember
  · have member := congrArg (fun region => region false) whole
    exact falseAbsent (member.mpr True.intro)

/-- Refutation: fiberwise probability measures do not imply joint measurability
of the law family. This refutes replacing joint kernel/law-family measurability
by pointwise normalization. -/
theorem probability_fibers_do_not_imply_measurability :
    (∀ point, Measure.IsProbability (pointLaws point).val) ∧
      ¬MeasurableMap (Space.indiscrete Bool) (space (Space.discrete Bool)) pointLaws :=
  ⟨fun point => (pointLaws point).property, pointLaws_not_measurable⟩

/-- The Giry probability law space on an empty carrier is standard Borel. -/
theorem empty_law_space_standardBorel :
    Nonempty (StandardBorel (space (Space.discrete Empty))) :=
  ⟨standardBorel (StandardBorel.ofEmpty (fun ⟨point⟩ => nomatch point))⟩

/-- The Giry probability law space on an empty carrier has an empty carrier
because probability measures require a nonempty carrier. -/
theorem empty_law_space_empty : ¬Nonempty (Law (Space.discrete Empty)) := by
  rintro ⟨law⟩
  obtain ⟨point⟩ := law.property.nonempty
  exact nomatch point

end Problib.Measure.Giry.Necessity
