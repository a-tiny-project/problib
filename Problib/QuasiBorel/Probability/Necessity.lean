import Problib.QuasiBorel.Probability.Monad

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability.Necessity

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)
open Problib.Real.Construction

private def boolean := Space.unrestricted (Source.ofMeasurable borel) Bool

private noncomputable def firstPresentation : Presentation boolean where
  random := fun _ => false
  accepted := True.intro
  sourceLaw := Giry.pure borel Dedekind.zero

private noncomputable def secondPresentation : Presentation boolean := by
  classical
  exact {
    random := fun seed => if seed = Dedekind.zero then false else true
    accepted := True.intro
    sourceLaw := Giry.pure borel Dedekind.zero
  }

/-- Distinct raw presentations can define the exact same probability law, showing raw presentations are strictly finer than laws. -/
theorem distinct_presentations_equal_law :
    firstPresentation ≠ secondPresentation ∧ firstPresentation.toLaw = secondPresentation.toLaw := by
  classical
  constructor
  · intro equal
    have pointwise := congrArg (fun presentation => presentation.random Dedekind.one) equal
    change false = (if Dedekind.one = Dedekind.zero then false else true) at pointwise
    rw [if_neg Dedekind.one_ne_zero] at pointwise
    exact Bool.false_ne_true pointwise
  · apply Law.ext
    change Giry.map firstPresentation.random (Space.random_measurable firstPresentation.accepted)
      (Giry.pure borel Dedekind.zero) =
      Giry.map secondPresentation.random (Space.random_measurable secondPresentation.accepted)
        (Giry.pure borel Dedekind.zero)
    rw [Giry.map_pure, Giry.map_pure]
    simp only [firstPresentation, secondPresentation, ite_true]

/-- The mapping from raw presentations to representable laws is not injective. -/
theorem presentation_toLaw_not_injective :
    ¬Function.Injective (@Presentation.toLaw boolean) := by
  intro injective
  exact distinct_presentations_equal_law.1 (injective distinct_presentations_equal_law.2)

/-- The empty quasi-Borel space carries no probability laws, reflecting normalization requirements. -/
theorem empty_has_no_probability_law :
    ¬Nonempty (Law (Space.unrestricted (Source.ofMeasurable borel) Empty)) := by
  intro existsLaw
  rcases (nonempty_iff _).mp existsLaw with ⟨point⟩
  exact Empty.elim point

end Problib.QuasiBorel.Probability.Necessity
