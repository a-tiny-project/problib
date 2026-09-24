module

public import Problib.Measure.Additive.Comap.Finite
public import Problib.Measure.Additive.Partition
public import Problib.Real.Extended.Additive

set_option autoImplicit false

namespace Problib.Measure.Necessity.Embedding

open Problib.Real

private theorem collapse_image (region : Set Bool) (input : Bool) (member : region input) :
    Set.image (fun _ : Bool => ()) region = Set.univ := by
  apply Set.ext
  intro output
  cases output
  exact ⟨fun _ => True.intro, fun _ => ⟨input, member, rfl⟩⟩

/-- Failure of direct image-based measure transport when injectivity is
omitted on a collapsing map. -/
public theorem collapse_image_formula_impossible :
    ¬∃ candidate : Measure (Space.discrete Bool), ∀ region,
      candidate region = (Measure.dirac (Space.discrete Unit) ())
        (Set.image (fun _ : Bool => ()) region) := by
  rintro ⟨candidate, values⟩
  have partition := candidate.add_complement
    (region := Set.singleton false) True.intro
  have left : candidate (Set.singleton false) = ENNReal.one := by
    rw [values, collapse_image (Set.singleton false) false rfl, Measure.dirac_apply_univ]
  have right : candidate (Set.complement (Set.singleton false)) = ENNReal.one := by
    rw [values, collapse_image (Set.complement (Set.singleton false)) true (by
      change ¬(true = false)
      decide), Measure.dirac_apply_univ]
  have whole : candidate Set.univ = ENNReal.one := by
    rw [values, collapse_image Set.univ false True.intro, Measure.dirac_apply_univ]
  rw [left, right, whole] at partition
  have equal : ENNReal.add ENNReal.one ENNReal.one =
      ENNReal.add ENNReal.one ENNReal.zero := by
    rw [ENNReal.add_zero]
    exact partition
  exact ENNReal.one_ne_zero
    (ENNReal.add_left_cancel_of_finite (factor := ENNReal.one) True.intro equal)

/-- Canonical measurable embedding of the empty subtype into the discrete
unit space. -/
@[expose] public def emptyInclusion :
    MeasurableEmbedding
      (Space.comap (fun value : {input : Unit // (Set.empty : Set Unit) input} => value.val)
        (Space.discrete Unit)) (Space.discrete Unit) :=
  MeasurableEmbedding.subtype Set.empty (Space.discrete Unit).empty

/-- The Dirac probability measure on unit space pulls to zero mass on the
empty subtype. -/
public theorem empty_subtype_mass :
    (Measure.dirac (Space.discrete Unit) ()).comap emptyInclusion Set.univ = ENNReal.zero := by
  rw [Measure.comap_apply_univ]
  change (Measure.dirac (Space.discrete Unit) ())
    (Set.range (MeasurableEmbedding.subtype Set.empty (Space.discrete Unit).empty).function) = _
  rw [MeasurableEmbedding.subtype_range, Measure.empty_apply]

/-- The empty subtype pullback of a probability measure fails to be a
probability measure. -/
public theorem empty_subtype_not_probability :
    ¬Measure.IsProbability ((Measure.dirac (Space.discrete Unit) ()).comap emptyInclusion) := by
  intro probability
  have mass := probability.univ_eq_one
  rw [empty_subtype_mass] at mass
  exact ENNReal.one_ne_zero mass.symm

public theorem empty_subtype_probability_input :
    Measure.IsProbability (Measure.dirac (Space.discrete Unit) ()) :=
  Measure.IsProbability.dirac (Space.discrete Unit) ()

/-- The zero pullback measure on the empty subtype remains s-finite. -/
public noncomputable def empty_subtype_sFinite :
    Measure.SFinite ((Measure.dirac (Space.discrete Unit) ()).comap emptyInclusion) :=
  (Measure.SFinite.ofFinite (Measure.IsFinite.dirac (Space.discrete Unit) ())).comap emptyInclusion

end Problib.Measure.Necessity.Embedding
