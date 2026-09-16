module

public import Foundations.Measure.Additive.AbsoluteContinuity
public import Foundations.Measure.Decomposition.ZeroInfinity.Properties

set_option autoImplicit false

/-!
# Zero-infinity absolute continuity

Defines zero-infinity absolute continuity, which requires ordinary absolute
continuity and preservation of reference zero-infinity sets.

The module establishes reflexivity, transitivity, and reduction to ordinary
absolute continuity under a sigma-finite reference measure.
The module also characterizes the relation through mismatch nullity given
greatest zero-infinity sets.
Provenance follows Matthijs Vákár and Luke Ong,
[arXiv:1810.01837v2](https://arxiv.org/pdf/1810.01837v2), Lemma 3.
-/

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A target measure is zero-infinity absolutely continuous with respect to a
reference measure if it is absolutely continuous and preserves reference
zero-infinity sets. -/
public structure ZeroInfinityAbsolutelyContinuous (target reference : Measure space) : Prop where
  absolutelyContinuous : AbsolutelyContinuous target reference
  preservesZeroInfinity : ∀ {region : Set alpha}, IsZeroInfinitySet reference region →
    IsZeroInfinitySet target region

/-- Reflexivity of zero-infinity absolute continuity. -/
public theorem ZeroInfinityAbsolutelyContinuous.refl (measure : Measure space) :
    ZeroInfinityAbsolutelyContinuous measure measure :=
  ⟨AbsolutelyContinuous.refl measure, fun zeroInfinity => zeroInfinity⟩

/-- Transitivity of zero-infinity absolute continuity. -/
public theorem ZeroInfinityAbsolutelyContinuous.trans {target middle reference : Measure space}
    (left : ZeroInfinityAbsolutelyContinuous target middle)
    (right : ZeroInfinityAbsolutelyContinuous middle reference) :
    ZeroInfinityAbsolutelyContinuous target reference :=
  ⟨AbsolutelyContinuous.trans left.absolutelyContinuous right.absolutelyContinuous,
    fun zeroInfinity => left.preservesZeroInfinity (right.preservesZeroInfinity zeroInfinity)⟩

/-- Given greatest zero-infinity sets for both measures, zero-infinity absolute
continuity is equivalent to ordinary absolute continuity and target-nullity of
the mismatch `referenceTop \ targetTop`. -/
public theorem ZeroInfinityAbsolutelyContinuous.iff_top_difference {target reference : Measure space}
    (targetTop : TopZeroInfinitySet target)
    (referenceTop : TopZeroInfinitySet reference) :
    ZeroInfinityAbsolutelyContinuous target reference ↔
      AbsolutelyContinuous target reference ∧
        target.NullSet (Set.difference referenceTop.set targetTop.set) := by
  constructor
  · intro continuous
    exact ⟨continuous.absolutelyContinuous, targetTop.greatest
      (continuous.preservesZeroInfinity referenceTop.zeroInfinity)⟩
  · rintro ⟨continuous, mismatch⟩
    refine ⟨continuous, ?_⟩
    intro region zeroInfinity
    apply IsZeroInfinitySet.of_null_difference zeroInfinity.measurable targetTop.zeroInfinity
    have excluded : target.NullSet (Set.difference region referenceTop.set) :=
      AbsolutelyContinuous.null continuous (referenceTop.greatest zeroInfinity)
    apply (excluded.union mismatch).mono
    intro value member
    classical
    by_cases inside : referenceTop.set value
    · exact Or.inr ⟨inside, member.2⟩
    · exact Or.inl ⟨member.1, inside⟩

/-- Under a sigma-finite reference measure, zero-infinity absolute continuity
reduces to ordinary absolute continuity. -/
public theorem ZeroInfinityAbsolutelyContinuous.iff_absolutelyContinuous_of_sigmaFinite
    {target reference : Measure space} (finite : SigmaFinite reference) :
    ZeroInfinityAbsolutelyContinuous target reference ↔ AbsolutelyContinuous target reference := by
  constructor
  · exact fun continuous => continuous.absolutelyContinuous
  · intro continuous
    refine ⟨continuous, ?_⟩
    intro region zeroInfinity
    have null : target.NullSet region :=
      AbsolutelyContinuous.null continuous (zeroInfinity.null_of_sigmaFinite finite)
    exact IsZeroInfinitySet.of_null zeroInfinity.measurable null

end Foundations.Measure.Measure
