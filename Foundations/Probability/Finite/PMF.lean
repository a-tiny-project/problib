import Foundations.Probability.Finite.Measure

namespace Foundations.Probability

universe u v w

structure FinitePMF (α : Type u) where
  measure : FiniteMeasure α
  total_one : measure.total = 1
deriving Repr

namespace FinitePMF

def prob {α : Type u} [DecidableEq α] (pmf : FinitePMF α) (point : α) : NNRat :=
  pmf.measure.mass point

def support {α : Type u} [DecidableEq α] (pmf : FinitePMF α) : FiniteSet α :=
  pmf.measure.support

def Equivalent {α : Type u} (left right : FinitePMF α) : Prop :=
  left.measure ≈ₘ right.measure

infix:50 " ≈ₚ " => Equivalent

def dirac {α : Type u} (value : α) : FinitePMF α where
  measure := FiniteMeasure.dirac value
  total_one := FiniteMeasure.total_dirac value

def map {α : Type u} {β : Type v} (mapValue : α → β) (pmf : FinitePMF α) : FinitePMF β where
  measure := FiniteMeasure.map mapValue pmf.measure
  total_one := by
    rw [FiniteMeasure.total_map, pmf.total_one]

def bind {α : Type u} {β : Type v} (pmf : FinitePMF α)
    (kernel : α → FinitePMF β) : FinitePMF β where
  measure := FiniteMeasure.bind pmf.measure fun value => (kernel value).measure
  total_one := by
    rw [FiniteMeasure.total_bind]
    calc
      pmf.measure.integral (fun value => (kernel value).measure.total) =
          pmf.measure.integral (fun _ => 1) := by
            apply FiniteMeasure.integral_congr
            intro value
            exact (kernel value).total_one
      _ = pmf.measure.total := FiniteMeasure.integral_one pmf.measure
      _ = 1 := pmf.total_one

def product {α : Type u} {β : Type v} (left : FinitePMF α) (right : FinitePMF β) :
    FinitePMF (α × β) :=
  bind left fun leftValue => map (fun rightValue => (leftValue, rightValue)) right

def marginal₁ {α : Type u} {β : Type v} (pmf : FinitePMF (α × β)) : FinitePMF α :=
  map Prod.fst pmf

def marginal₂ {α : Type u} {β : Type v} (pmf : FinitePMF (α × β)) : FinitePMF β :=
  map Prod.snd pmf

def score {α : Type u} (pmf : FinitePMF α) (factor : α → NNRat) : FiniteMeasure α :=
  pmf.measure.reweight factor

def restrict {α : Type u} (pmf : FinitePMF α) (event : α → Prop)
    [DecidablePred event] : FiniteMeasure α :=
  score pmf fun value => if event value then 1 else 0

def normalize {α : Type u} (measure : FiniteMeasure α) (nonzero : measure.total ≠ 0) :
    FinitePMF α where
  measure := measure.scale (NNRat.inverse measure.total nonzero)
  total_one := by
    rw [FiniteMeasure.total_scale, NNRat.inverse_mul_self]

def normalize? {α : Type u} (measure : FiniteMeasure α) : Option (FinitePMF α) :=
  if nonzero : measure.total = 0 then
    none
  else
    some (normalize measure nonzero)

def condition {α : Type u} (pmf : FinitePMF α) (event : α → Prop)
    [DecidablePred event] (nonzero : (restrict pmf event).total ≠ 0) : FinitePMF α :=
  normalize (restrict pmf event) nonzero

def condition? {α : Type u} (pmf : FinitePMF α) (event : α → Prop)
    [DecidablePred event] : Option (FinitePMF α) :=
  normalize? (restrict pmf event)

theorem Equivalent.refl {α : Type u} (pmf : FinitePMF α) : pmf ≈ₚ pmf :=
  FiniteMeasure.Equivalent.refl pmf.measure

theorem Equivalent.symm {α : Type u} {left right : FinitePMF α}
    (equivalent : left ≈ₚ right) : right ≈ₚ left :=
  FiniteMeasure.Equivalent.symm equivalent

theorem Equivalent.trans {α : Type u} {first second third : FinitePMF α}
    (firstSecond : first ≈ₚ second) (secondThird : second ≈ₚ third) : first ≈ₚ third :=
  FiniteMeasure.Equivalent.trans firstSecond secondThird

def equivalentSetoid (α : Type u) : Setoid (FinitePMF α) where
  r := Equivalent
  iseqv := by
    constructor
    · intro pmf
      exact Equivalent.refl pmf
    · intro left right equivalent
      exact Equivalent.symm equivalent
    · intro first second third firstSecond secondThird
      exact Equivalent.trans firstSecond secondThird

@[simp] theorem prob_dirac {α : Type u} [DecidableEq α] (value point : α) :
    (dirac value).prob point = if value = point then 1 else 0 :=
  FiniteMeasure.mass_dirac value point

theorem prob_zero_outside_support {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (point : α) (absent : point ∉ pmf.support) :
    pmf.prob point = 0 :=
  FiniteMeasure.mass_zero_outside_support pmf.measure point absent

theorem prob_map {α : Type u} {β : Type v} [DecidableEq β]
    (mapValue : α → β) (pmf : FinitePMF α) (point : β) :
    (map mapValue pmf).prob point =
      pmf.measure.integral fun value => if mapValue value = point then 1 else 0 :=
  FiniteMeasure.mass_map mapValue pmf.measure point

theorem prob_map_injective {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (mapValue : α → β) (injective : ∀ {left right}, mapValue left = mapValue right → left = right)
    (pmf : FinitePMF α) (point : α) :
    (map mapValue pmf).prob (mapValue point) = pmf.prob point :=
  FiniteMeasure.mass_map_injective mapValue injective pmf.measure point

theorem prob_bind {α : Type u} {β : Type v} [DecidableEq β]
    (pmf : FinitePMF α) (kernel : α → FinitePMF β) (point : β) :
    (bind pmf kernel).prob point =
      pmf.measure.integral fun value => (kernel value).prob point :=
  FiniteMeasure.mass_bind pmf.measure (fun value => (kernel value).measure) point

theorem score_total {α : Type u} (pmf : FinitePMF α) (factor : α → NNRat) :
    (score pmf factor).total = pmf.measure.integral factor :=
  FiniteMeasure.total_reweight pmf.measure factor

theorem restrict_total_zero_of_disjoint_support {α : Type u} [DecidableEq α]
    (pmf : FinitePMF α) (event : α → Prop) [DecidablePred event]
    (disjoint : ∀ value, value ∈ pmf.support → ¬ event value) :
    (restrict pmf event).total = 0 := by
  rw [restrict, score_total]
  apply FiniteMeasure.integral_zero_of_zero_on_support
  intro value member
  simp [disjoint value member]

theorem score_mass {α : Type u} [DecidableEq α] (pmf : FinitePMF α)
    (factor : α → NNRat) (point : α) :
    (score pmf factor).mass point = pmf.prob point * factor point :=
  FiniteMeasure.mass_reweight pmf.measure factor point

theorem normalize_mass {α : Type u} [DecidableEq α] (measure : FiniteMeasure α)
    (nonzero : measure.total ≠ 0) (point : α) :
    (normalize measure nonzero).prob point =
      NNRat.inverse measure.total nonzero * measure.mass point :=
  FiniteMeasure.mass_scale _ measure point

@[simp] theorem normalize?_of_zero {α : Type u} (measure : FiniteMeasure α)
    (zeroTotal : measure.total = 0) : normalize? measure = none := by
  simp [normalize?, zeroTotal]

@[simp] theorem normalize?_of_nonzero {α : Type u} (measure : FiniteMeasure α)
    (nonzero : measure.total ≠ 0) : normalize? measure = some (normalize measure nonzero) := by
  simp [normalize?, nonzero]

theorem Equivalent.map {α : Type u} {β : Type v} {left right : FinitePMF α}
    (equivalent : left ≈ₚ right) (transform : α → β) :
    map transform left ≈ₚ map transform right :=
  FiniteMeasure.Equivalent.map equivalent transform

theorem Equivalent.bind {α : Type u} {β : Type v}
    {left right : FinitePMF α} {leftKernel rightKernel : α → FinitePMF β}
    (measures : left ≈ₚ right) (kernels : ∀ value, leftKernel value ≈ₚ rightKernel value) :
    bind left leftKernel ≈ₚ bind right rightKernel :=
  FiniteMeasure.Equivalent.bind measures kernels

theorem map_id {α : Type u} (pmf : FinitePMF α) :
    map (fun value => value) pmf ≈ₚ pmf :=
  FiniteMeasure.map_id pmf.measure

theorem map_comp {α : Type u} {β : Type v} {γ : Type w}
    (first : α → β) (second : β → γ) (pmf : FinitePMF α) :
    map second (map first pmf) ≈ₚ map (fun value => second (first value)) pmf :=
  FiniteMeasure.map_comp first second pmf.measure

theorem bind_dirac_left {α : Type u} {β : Type v}
    (value : α) (kernel : α → FinitePMF β) :
    bind (dirac value) kernel ≈ₚ kernel value :=
  FiniteMeasure.bind_dirac_left value (fun input => (kernel input).measure)

theorem bind_dirac_right {α : Type u} (pmf : FinitePMF α) :
    bind pmf dirac ≈ₚ pmf :=
  FiniteMeasure.bind_dirac_right pmf.measure

theorem bind_dirac_map {α : Type u} {β : Type v}
    (pmf : FinitePMF α) (transform : α → β) :
    bind pmf (fun value => dirac (transform value)) ≈ₚ map transform pmf := by
  intro integrand
  change (FiniteMeasure.bind pmf.measure (fun value =>
      FiniteMeasure.dirac (transform value))).integral integrand =
    (FiniteMeasure.map transform pmf.measure).integral integrand
  rw [FiniteMeasure.integral_bind, FiniteMeasure.integral_map]
  apply FiniteMeasure.integral_congr
  intro value
  rw [FiniteMeasure.integral_dirac]

theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (pmf : FinitePMF α) (first : α → FinitePMF β) (second : β → FinitePMF γ) :
    bind (bind pmf first) second ≈ₚ bind pmf (fun value => bind (first value) second) :=
  FiniteMeasure.bind_assoc pmf.measure (fun value => (first value).measure)
    (fun value => (second value).measure)

theorem bind_commute {α : Type u} {β : Type v} {γ : Type w}
    (left : FinitePMF α) (right : FinitePMF β)
    (kernel : α → β → FinitePMF γ) :
    bind left (fun leftValue => bind right (kernel leftValue)) ≈ₚ
      bind right (fun rightValue => bind left (fun leftValue =>
        kernel leftValue rightValue)) :=
  FiniteMeasure.bind_commute left.measure right.measure fun leftValue rightValue =>
    (kernel leftValue rightValue).measure

end FinitePMF

end Foundations.Probability
