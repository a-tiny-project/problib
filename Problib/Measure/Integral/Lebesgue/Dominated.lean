module

public import Problib.Measure.Integral.Lebesgue.Infimum
public import Problib.Measure.Extended.Order

/-! Fatou's lemma and dominated convergence for the lower integral.

`lintegral_iSup` gives continuity from below and `lintegral_iInf` gives it from
above under a finite term. Fatou is the first read off a monotone envelope, its
reverse is the second, and dominated convergence is the two of them closing on
each other. The lower and upper limits are built from the `iSup` and `iInf` of
`Problib.Real.Extended.Indexed`, and are stated here beside their only
consumer rather than in that module, which owns no limit notion.

No sequence here is assumed convergent in a topological sense. A caller states
pointwise convergence by giving the lower and upper limits the same value, which
is the form every hypothesis below takes.
-/

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- The lower limit of an extended-nonnegative sequence. -/
@[expose] public noncomputable def liminf (values : Nat → ENNReal) : ENNReal :=
  iSup (fun stage => iInf (fun offset => values (stage + offset)))

/-- The upper limit of an extended-nonnegative sequence. -/
@[expose] public noncomputable def limsup (values : Nat → ENNReal) : ENNReal :=
  iInf (fun stage => iSup (fun offset => values (stage + offset)))

/-- Tails of the lower envelope increase. -/
public theorem liminf_tail_mono (values : Nat → ENNReal) (stage : Nat) :
    le (iInf (fun offset => values (stage + offset)))
      (iInf (fun offset => values (stage + 1 + offset))) := by
  apply le_iInf
  intro offset
  have shifted : stage + 1 + offset = stage + (1 + offset) := by
    omega
  rw [shifted]
  exact iInf_le (fun position => values (stage + position)) (1 + offset)

/-- Tails of the upper envelope decrease. -/
public theorem limsup_tail_anti (values : Nat → ENNReal) (stage : Nat) :
    le (iSup (fun offset => values (stage + 1 + offset)))
      (iSup (fun offset => values (stage + offset))) := by
  apply iSup_le
  intro offset
  have shifted : stage + 1 + offset = stage + (1 + offset) := by
    omega
  rw [shifted]
  exact le_iSup (fun position => values (stage + position)) (1 + offset)

/-- The lower limit never exceeds the upper limit. -/
public theorem liminf_le_limsup (values : Nat → ENNReal) :
    le (liminf values) (limsup values) := by
  apply iSup_le
  intro lowerStage
  apply le_iInf
  intro upperStage
  have crossed : lowerStage + upperStage = upperStage + lowerStage := by omega
  refine le_trans (iInf_le (fun offset => values (lowerStage + offset)) upperStage) ?_
  rw [crossed]
  exact le_iSup (fun offset => values (upperStage + offset)) lowerStage

/-- A uniform upper bound bounds the upper limit. -/
public theorem limsup_le {values : Nat → ENNReal} {bound : ENNReal}
    (bounded : ∀ index, le (values index) bound) : le (limsup values) bound :=
  le_trans (iInf_le (fun stage => iSup (fun offset => values (stage + offset))) 0)
    (iSup_le (fun offset => bounded (0 + offset)))

/-- A uniform lower bound bounds the lower limit. -/
public theorem le_liminf {values : Nat → ENNReal} {bound : ENNReal}
    (bounded : ∀ index, le bound (values index)) : le bound (liminf values) :=
  le_trans (le_iInf (fun offset => bounded (0 + offset)))
    (le_iSup (fun stage => iInf (fun offset => values (stage + offset))) 0)

/-- A constant sequence has its value as lower limit. -/
public theorem liminf_const (value : ENNReal) : liminf (fun _ => value) = value := by
  apply le_antisymm
  · exact iSup_le (fun _ => iInf_le (fun _ => value) 0)
  · exact le_liminf (fun _ => le_refl value)

/-- A constant sequence has its value as upper limit. -/
public theorem limsup_const (value : ENNReal) : limsup (fun _ => value) = value := by
  apply le_antisymm
  · exact limsup_le (fun _ => le_refl value)
  · exact le_iInf (fun _ => le_iSup (fun _ => value) 0)

/-- A bound that holds from some stage on bounds the upper limit. -/
public theorem limsup_le_of_eventually {values : Nat → ENNReal} {bound : ENNReal}
    (eventually : ∃ stage, ∀ offset, le (values (stage + offset)) bound) :
    le (limsup values) bound := by
  rcases eventually with ⟨stage, bounded⟩
  exact le_trans (iInf_le (fun stage => iSup (fun offset => values (stage + offset))) stage)
    (iSup_le bounded)

/-- A bound that holds from some stage on bounds the lower limit below. -/
public theorem le_liminf_of_eventually {values : Nat → ENNReal} {bound : ENNReal}
    (eventually : ∃ stage, ∀ offset, le bound (values (stage + offset))) :
    le bound (liminf values) := by
  rcases eventually with ⟨stage, bounded⟩
  exact le_trans (le_iInf bounded)
    (le_iSup (fun stage => iInf (fun offset => values (stage + offset))) stage)

/-- An upper limit strictly below a bound puts the whole sequence strictly below
it from some stage on. -/
public theorem eventually_lt_of_limsup_lt {values : Nat → ENNReal} {bound : ENNReal}
    (below : lt (limsup values) bound) :
    ∃ stage, ∀ offset, lt (values (stage + offset)) bound := by
  rcases exists_index_less_of_iInf_lt below with ⟨stage, tailBelow⟩
  refine ⟨stage, fun offset => ?_⟩
  have within := le_iSup (fun position => values (stage + position)) offset
  exact ⟨le_trans within tailBelow.left, fun back => tailBelow.right (le_trans back within)⟩

end Problib.Real.ENNReal

namespace Problib.Measure

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- Fatou's lemma: the integral of the lower limit never exceeds the lower limit
of the integrals. No domination and no finiteness is needed. -/
public theorem lintegral_liminf_le (measure : Measure space)
    (functions : Nat → α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index)) :
    ENNReal.le
      (lintegral measure
        (fun input => ENNReal.liminf (fun index => functions index input)))
      (ENNReal.liminf (fun index => lintegral measure (functions index))) := by
  let envelope := fun stage input =>
    ENNReal.iInf (fun offset => functions (stage + offset) input)
  have envelopeMeasurable : ∀ stage, ENNRealMeasurable space (envelope stage) :=
    fun stage => ENNRealMeasurable.iInf (fun offset => measurable (stage + offset))
  have envelopeMono : ∀ stage input,
      ENNReal.le (envelope stage input) (envelope (stage + 1) input) :=
    fun stage input =>
      ENNReal.liminf_tail_mono (fun index => functions index input) stage
  have exchange := lintegral_iSup measure envelope envelopeMeasurable envelopeMono
  have rewritten : (fun input => ENNReal.liminf (fun index => functions index input)) =
      fun input => ENNReal.iSup (fun stage => envelope stage input) := rfl
  rw [rewritten, exchange]
  apply ENNReal.iSup_le
  intro stage
  refine ENNReal.le_trans ?_
    (ENNReal.le_iSup
      (fun position => ENNReal.iInf
        (fun offset => lintegral measure (functions (position + offset)))) stage)
  apply ENNReal.le_iInf
  intro offset
  apply lintegral_mono
  intro input
  exact ENNReal.iInf_le (fun position => functions (stage + position) input) offset

/-- The reverse of Fatou's lemma under a dominating function of finite
integral: the upper limit of the integrals never exceeds the integral of the
upper limit. -/
public theorem limsup_le_lintegral_limsup (measure : Measure space)
    (functions : Nat → α → ENNReal) (dominator : α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index))
    (dominated : ∀ index input, ENNReal.le (functions index input) (dominator input))
    (dominatorFinite : ENNReal.Finite (lintegral measure dominator)) :
    ENNReal.le
      (ENNReal.limsup (fun index => lintegral measure (functions index)))
      (lintegral measure
        (fun input => ENNReal.limsup (fun index => functions index input))) := by
  let envelope := fun stage input =>
    ENNReal.iSup (fun offset => functions (stage + offset) input)
  have envelopeMeasurable : ∀ stage, ENNRealMeasurable space (envelope stage) :=
    fun stage => ENNRealMeasurable.iSup (fun offset => measurable (stage + offset))
  have envelopeAnti : ∀ stage input,
      ENNReal.le (envelope (stage + 1) input) (envelope stage input) :=
    fun stage input =>
      ENNReal.limsup_tail_anti (fun index => functions index input) stage
  have envelopeBelow : ∀ stage input,
      ENNReal.le (envelope stage input) (dominator input) :=
    fun stage input => ENNReal.iSup_le (fun offset => dominated (stage + offset) input)
  have envelopeFinite : ∃ stage, ENNReal.Finite (lintegral measure (envelope stage)) :=
    ⟨0, ENNReal.finite_of_le (lintegral_mono measure (envelopeBelow 0)) dominatorFinite⟩
  have exchange := lintegral_iInf measure envelope envelopeMeasurable
    envelopeAnti envelopeFinite
  have rewritten : (fun input => ENNReal.limsup (fun index => functions index input)) =
      fun input => ENNReal.iInf (fun stage => envelope stage input) := rfl
  rw [rewritten, exchange]
  apply ENNReal.iInf_mono
  intro stage
  apply ENNReal.iSup_le
  intro offset
  apply lintegral_mono
  intro input
  exact ENNReal.le_iSup (fun position => functions (stage + position) input) offset

/-- Dominated convergence for the lower integral. A sequence dominated by one
function of finite integral has its integrals converging to the integral of the
common pointwise limit, where convergence is stated by the lower and upper
limits agreeing. -/
public theorem lintegral_dominated_convergence (measure : Measure space)
    (functions : Nat → α → ENNReal) (limit dominator : α → ENNReal)
    (measurable : ∀ index, ENNRealMeasurable space (functions index))
    (dominated : ∀ index input, ENNReal.le (functions index input) (dominator input))
    (dominatorFinite : ENNReal.Finite (lintegral measure dominator))
    (lower : ∀ input,
      ENNReal.liminf (fun index => functions index input) = limit input)
    (upper : ∀ input,
      ENNReal.limsup (fun index => functions index input) = limit input) :
    ENNReal.liminf (fun index => lintegral measure (functions index)) =
        lintegral measure limit ∧
      ENNReal.limsup (fun index => lintegral measure (functions index)) =
        lintegral measure limit := by
  have below : ENNReal.le (lintegral measure limit)
      (ENNReal.liminf (fun index => lintegral measure (functions index))) := by
    have fatou := lintegral_liminf_le measure functions measurable
    rwa [funext lower] at fatou
  have above : ENNReal.le
      (ENNReal.limsup (fun index => lintegral measure (functions index)))
      (lintegral measure limit) := by
    have reverse := limsup_le_lintegral_limsup measure functions dominator
      measurable dominated dominatorFinite
    rwa [funext upper] at reverse
  have ordered := ENNReal.liminf_le_limsup
    (fun index => lintegral measure (functions index))
  exact ⟨ENNReal.le_antisymm (ENNReal.le_trans ordered above) below,
    ENNReal.le_antisymm above (ENNReal.le_trans below ordered)⟩

end Problib.Measure
