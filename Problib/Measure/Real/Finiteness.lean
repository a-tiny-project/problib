module

public import Problib.Measure.Real.Lebesgue
public import Problib.Measure.Additive.SFinite

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

/-- Closed bounded intervals give an explicit finite-mass cover of the real line. -/
public noncomputable def volumeFiniteCover : Measure.FiniteCover volume where
  sets := fun index => Icc (Dedekind.neg (Dedekind.selection.ofRat (index : Rat)))
    (Dedekind.selection.ofRat (index : Rat))
  measurable := fun index => measurable_icc _ _
  finite := fun index => by
    rw [volume_icc]
    exact ENNReal.ofReal_finite _
  cover := by
    apply Set.ext
    intro value
    constructor
    · intro _
      exact True.intro
    · intro _
      rcases Dedekind.exists_nat_upper value with ⟨first, upper⟩
      rcases Dedekind.exists_nat_upper (Dedekind.neg value) with ⟨second, lower⟩
      let index := max first second
      have firstLe : Dedekind.le (Dedekind.selection.ofRat (first : Rat))
          (Dedekind.selection.ofRat (index : Rat)) :=
        (Dedekind.ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr (Nat.le_max_left _ _))
      have secondLe : Dedekind.le (Dedekind.selection.ofRat (second : Rat))
          (Dedekind.selection.ofRat (index : Rat)) :=
        (Dedekind.ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr (Nat.le_max_right _ _))
      refine ⟨index, ?_, Dedekind.le_trans upper firstLe⟩
      have reflected := Dedekind.neg_le_neg_iff.mpr (Dedekind.le_trans lower secondLe)
      simpa only [Dedekind.neg_neg] using reflected

/-- Lebesgue volume is sigma-finite, with an explicit exhaustion certificate. -/
public noncomputable def volumeSigmaFinite : Measure.SigmaFinite volume :=
  Measure.SigmaFinite.ofCover volumeFiniteCover

/-- Lebesgue volume has the s-finite presentation required by Tonelli and kernels. -/
public noncomputable def volumeSFinite : Measure.SFinite volume :=
  volumeSigmaFinite.toSFinite

end Problib.Measure.Real
