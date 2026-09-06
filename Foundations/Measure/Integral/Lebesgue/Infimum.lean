module

public import Foundations.Measure.Integral.Lebesgue.Subtract
public import Foundations.Real.Extended.Infimum

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u

variable {α : Type u} {space : Space α}

private theorem lintegral_iInf_of_initial_finite (measure : Measure space) (functions : Nat → α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index))
    (antitone : ∀ {first second}, first ≤ second → ∀ input,
      ENNReal.le (functions second input) (functions first input))
    (initialFinite : ENNReal.Finite (lintegral measure (functions 0))) :
    lintegral measure (fun input => ENNReal.iInf (fun index => functions index input)) =
      ENNReal.iInf (fun index => lintegral measure (functions index)) := by
  let limit := fun input => ENNReal.iInf (fun index => functions index input)
  let difference := fun index input => ENNReal.sub (functions 0 input) (functions index input)
  have belowInitial : ∀ index input, ENNReal.le (functions index input) (functions 0 input) :=
    fun index => antitone (Nat.zero_le index)
  have eachFinite : ∀ index, ENNReal.Finite (lintegral measure (functions index)) :=
    fun index => ENNReal.finiteOfLe (lintegral_mono measure (belowInitial index)) initialFinite
  have limitBelow : ∀ input, ENNReal.le (limit input) (functions 0 input) :=
    fun input => ENNReal.iInfLe (fun index => functions index input) 0
  have limitMeasurable : ENNRealMeasurable space limit := ENNRealMeasurable.iInf measurable
  have limitFinite : ENNReal.Finite (lintegral measure limit) :=
    ENNReal.finiteOfLe (lintegral_mono measure limitBelow) initialFinite
  have differenceMeasurable : ∀ index, ENNRealMeasurable space (difference index) :=
    fun index => ENNRealMeasurable.sub (measurable 0) (measurable index)
  have continuous := lintegral_iSup measure difference differenceMeasurable
    (fun index input => ENNReal.subLeSubLeft (antitone (Nat.le_succ index) input) (functions 0 input))
  have pointwise : (fun input => ENNReal.iSup (fun index => difference index input)) =
      (fun input => ENNReal.sub (functions 0 input) (limit input)) :=
    funext fun input => (ENNReal.subIInf (functions 0 input) (fun index => functions index input)).symm
  rw [pointwise, lintegral_sub measure (measurable 0) limitMeasurable limitFinite limitBelow] at continuous
  have differences : (fun index => lintegral measure (difference index)) =
      (fun index => ENNReal.sub (lintegral measure (functions 0)) (lintegral measure (functions index))) :=
    funext fun index => lintegral_sub measure (measurable 0) (measurable index) (eachFinite index) (belowInitial index)
  rw [differences, ← ENNReal.subIInf] at continuous
  have infimumBelow : ENNReal.le (ENNReal.iInf (fun index => lintegral measure (functions index)))
      (lintegral measure (functions 0)) := ENNReal.iInfLe _ 0
  have comparison := congrArg (fun value => ENNReal.sub (lintegral measure (functions 0)) value) continuous
  have double (value : ENNReal) (bound : ENNReal.le value (lintegral measure (functions 0))) :
      ENNReal.sub (lintegral measure (functions 0))
        (ENNReal.sub (lintegral measure (functions 0)) value) = value := by
    have subtractionFinite := ENNReal.subFiniteOfFiniteLeft (right := value) initialFinite
    calc
      ENNReal.sub (lintegral measure (functions 0))
          (ENNReal.sub (lintegral measure (functions 0)) value) =
          ENNReal.sub (ENNReal.add (ENNReal.sub (lintegral measure (functions 0)) value) value)
            (ENNReal.sub (lintegral measure (functions 0)) value) :=
        congrArg (fun upper => ENNReal.sub upper (ENNReal.sub (lintegral measure (functions 0)) value))
          (ENNReal.subAddCancel bound).symm
      _ = value := ENNReal.addSubCancelLeft subtractionFinite
  rw [double _ (lintegral_mono measure limitBelow), double _ infimumBelow] at comparison
  exact comparison

/-- Continuity of the lower integral from above for pointwise decreasing
measurable sequences with at least one term of finite integral. -/
public theorem lintegral_iInf (measure : Measure space) (functions : Nat → α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index))
    (step : ∀ index input,
      ENNReal.le (functions (index + 1) input) (functions index input))
    (finiteTerm : ∃ index, ENNReal.Finite (lintegral measure (functions index))) :
    lintegral measure (fun input => ENNReal.iInf (fun index => functions index input)) =
      ENNReal.iInf (fun index => lintegral measure (functions index)) := by
  have antitone : ∀ {first second}, first ≤ second → ∀ input,
      ENNReal.le (functions second input) (functions first input) := by
    intro first second
    induction second with
    | zero =>
        intro included input
        have equal := Nat.eq_zero_of_le_zero included
        subst first
        exact ENNReal.leRefl _
    | succ index induction =>
        intro included input
        rcases Nat.lt_or_eq_of_le included with less | equal
        · exact ENNReal.leTrans (step index input)
            (induction (Nat.le_of_lt_succ less) input)
        · subst first
          exact ENNReal.leRefl _
  rcases finiteTerm with ⟨offset, finite⟩
  have pointwise : (fun input => ENNReal.iInf (fun index => functions (offset + index) input)) =
      (fun input => ENNReal.iInf (fun index => functions index input)) :=
    funext fun input => ENNReal.iInfTail (fun index => functions index input)
      (fun included => antitone included input) offset
  have continuous := lintegral_iInf_of_initial_finite measure (fun index => functions (offset + index))
    (fun index => measurable (offset + index))
    (fun included => antitone (Nat.add_le_add_left included offset))
    (by simpa only [Nat.add_zero] using finite)
  rw [pointwise] at continuous
  exact continuous.trans (ENNReal.iInfTail (fun index => lintegral measure (functions index))
    (fun included => lintegral_mono measure (antitone included)) offset)

/-- Continuity of the lower integral from above for almost-everywhere decreasing
measurable sequences with at least one term of finite integral. -/
public theorem lintegral_iInf_ae (measure : Measure space) (functions : Nat → α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index))
    (antitone : ∀ index, measure.AE (fun input =>
      ENNReal.le (functions (index + 1) input) (functions index input)))
    (finiteTerm : ∃ index, ENNReal.Finite (lintegral measure (functions index))) :
    lintegral measure (fun input => ENNReal.iInf (fun index => functions index input)) =
      ENNReal.iInf (fun index => lintegral measure (functions index)) := by
  classical
  rcases (Measure.ae_all_iff.mpr antitone).exists_null_exception with
    ⟨exceptional, exceptionalMeasurable, exceptionalNull, outside⟩
  let adjusted := fun index => ennrealPiecewise exceptional
    (fun _ => ENNReal.zero) (functions index)
  have adjustedMeasurable : ∀ index, ENNRealMeasurable space (adjusted index) :=
    fun index => ENNRealMeasurable.piecewise exceptionalMeasurable
      (ENNRealMeasurable.constant space ENNReal.zero) (measurable index)
  have adjustedStep : ∀ index input,
      ENNReal.le (adjusted (index + 1) input) (adjusted index input) := by
    intro index input
    by_cases member : exceptional input
    · simp only [adjusted, ennrealPiecewise, if_pos member]
      exact ENNReal.leRefl _
    · simp only [adjusted, ennrealPiecewise, if_neg member]
      exact outside input member index
  have outsideAE : measure.AE (fun input => ¬exceptional input) := by
    apply exceptionalNull.mono
    intro input member
    exact Classical.not_not.mp member
  have same : measure.AE (fun input => ∀ index, adjusted index input = functions index input) :=
    outsideAE.mono (fun input member index => by
      simp only [adjusted, ennrealPiecewise, if_neg member])
  have integrals : ∀ index,
      lintegral measure (adjusted index) = lintegral measure (functions index) :=
    fun index => lintegral_congr_ae (same.mono (fun _ equal => equal index))
  have limit : measure.AEEq
      (fun input => ENNReal.iInf (fun index => adjusted index input))
      (fun input => ENNReal.iInf (fun index => functions index input)) :=
    same.mono (fun _ equal => congrArg ENNReal.iInf (funext equal))
  have adjustedFinite : ∃ index, ENNReal.Finite (lintegral measure (adjusted index)) := by
    rcases finiteTerm with ⟨index, finite⟩
    exact ⟨index, integrals index ▸ finite⟩
  have result := lintegral_iInf measure adjusted adjustedMeasurable
    adjustedStep adjustedFinite
  rw [lintegral_congr_ae limit, funext integrals] at result
  exact result

end Foundations.Measure
