module

public import Problib.Measure.Kernel.Piecewise
public import Problib.Measure.Kernel.Composition.Bind
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Additive.Dirac
public import Problib.Measure.Additive.Algebra
public import Problib.Measure.AlmostEverywhere.Basic
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Real.Extended.Multiplication
public import Problib.Real.Nonnegative.Finite
public import Problib.Algebra.Sum

/-! Site moves from a finite disintegration.

A target disintegrates at a site when it is a law of contexts followed by a
finite reinsertion: at each context finitely many slots, each with a finite
weight, and the point that inserting the slot into the context gives
(`FiniteSite`, the sum form `target = ν.bind F.mass`). The site move deletes the
site from the current point and draws a slot with probability its share of the
context's total weight. At a context of total zero it runs any fallback kernel.

The move leaves the target invariant whatever the fallback does, since the
contexts of total zero carry no mass (`kernel_invariant`). Any kernel that agrees
with the draw at every point of positive total does too (`invariant_of_agrees`),
and the draw puts each slot's share on its insertion (`draw_insert`). A loop
over runtime slots meets this interface: the slots are a list of at most `bound`
entries, and the draw is a categorical draw over their weights.

A density that factors at the site, an outer factor of the context times a local
factor of the slot, keeps the sum form: the weighted target disintegrates over
the context law weighted by the outer factor, with each slot's weight times its
local factor (`reweight`, `withDensity_sum`). This is how a collapsed posterior
inherits the prior's site disintegration.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Site

open Problib.Real

universe u v w

variable {β : Type u} {γ : Type v} {σ : Type w} {X : Space β} {C : Space γ}

/-- A finite disintegration of a target at one site: a deletion to a context, a
reinsertion of a slot value, and finitely many slots per context with finite
weights, at most `bound` of them. Inserting a slot into a valid context and
deleting it again gives the context back. -/
public structure FiniteSite (X : Space β) (C : Space γ) (σ : Type w) where
  delete : β → γ
  delete_measurable : MeasurableMap X C delete
  context_discrete : ∀ set, C.Measurable set
  insert : γ → σ → β
  slots : γ → List σ
  bound : Nat
  slots_length : ∀ c, (slots c).length ≤ bound
  weight : γ → σ → NNReal
  Valid : γ → Prop
  delete_insert : ∀ {c}, Valid c → ∀ a, a ∈ slots c → delete (insert c a) = c

namespace FiniteSite

variable (F : FiniteSite X C σ)

/-- Every function out of a space whose sets are all measurable is measurable. -/
public theorem measurable_of_discrete (discrete : ∀ set, C.Measurable set)
    (function : γ → ENNReal) :
    ENNRealMeasurable C function :=
  fun _ => discrete _

/-- The total weight of a context's slots. -/
@[expose] public noncomputable def total (c : γ) : NNReal :=
  NNReal.additiveLaws.listSum ((F.slots c).map (F.weight c))

/-- The point masses at a context's insertions, each scaled by a factor. -/
@[expose] public noncomputable def spread (c : γ) (factor : σ → ENNReal) : Measure X :=
  Measure.listSum ((F.slots c).map fun a =>
    Measure.smul (factor a) (Measure.dirac X (F.insert c a)))

/-- The unnormalized reinsertion at a context: each slot's insertion carries its
weight. This is the summand of the sum form. -/
@[expose] public noncomputable def mass : Kernel C X where
  toFun c := F.spread c fun a => ENNReal.finite (F.weight c a)
  measurable _ := measurable_of_discrete F.context_discrete _

/-- A slot's share of its context's total weight. -/
@[expose] public noncomputable def share (c : γ) (a : σ) : ENNReal :=
  ENNReal.finite (NNReal.div (F.weight c a) (F.total c))

/-- The site draw at a context: each slot's insertion carries its share. -/
@[expose] public noncomputable def draw (c : γ) : Measure X :=
  F.spread c (F.share c)

/-- The site draw at the context of the current point. -/
@[expose] public noncomputable def drawKernel : Kernel X X where
  toFun x := F.draw (F.delete x)
  measurable {set} _ := ENNRealMeasurable.comp (map := fun c => F.draw c set)
    (measurable_of_discrete F.context_discrete _) F.delete_measurable

/-- The points whose context has total weight zero. -/
@[expose] public def zeroTotal : Set β := fun x => F.total (F.delete x) = NNReal.zero

public theorem zeroTotal_measurable : X.Measurable F.zeroTotal :=
  F.delete_measurable (F.context_discrete fun c => F.total c = NNReal.zero)

/-- The site move: the draw at the deleted context, and `fallback` at total zero. -/
@[expose] public noncomputable def kernel (fallback : Kernel X X) : Kernel X X :=
  Kernel.piecewise F.zeroTotal F.zeroTotal_measurable fallback F.drawKernel

public theorem kernel_zero (fallback : Kernel X X) {x : β}
    (zero : F.total (F.delete x) = NNReal.zero) : F.kernel fallback x = fallback x := by
  unfold kernel
  exact Kernel.piecewise_apply_of_mem F.zeroTotal F.zeroTotal_measurable fallback F.drawKernel x
    zero

public theorem kernel_positive (fallback : Kernel X X) {x : β}
    (positive : F.total (F.delete x) ≠ NNReal.zero) :
    F.kernel fallback x = F.draw (F.delete x) := by
  unfold kernel
  exact Kernel.piecewise_apply_of_not_mem F.zeroTotal F.zeroTotal_measurable fallback F.drawKernel x
    positive

/-- A spread's mass on a measurable set sums each factor at the insertions in it. -/
public theorem spread_apply (c : γ) (factor : σ → ENNReal) {set : Set β}
    (measurable : X.Measurable set) :
    F.spread c factor set = ENNReal.additiveLaws.listSum ((F.slots c).map fun a =>
      ENNReal.mul (factor a) (Measure.dirac X (F.insert c a) set)) := by
  rw [spread, Measure.listSum_apply _ measurable, List.map_map]
  exact ENNReal.additiveLaws.listSum_map_congr _ fun a _ =>
    Measure.smul_apply_measurable _ _ measurable

/-- Integrating against a spread sums each factor times the integrand at the
insertions. -/
public theorem lintegral_spread (c : γ) (factor : σ → ENNReal) {function : β → ENNReal}
    (measurable : ENNRealMeasurable X function) :
    lintegral (F.spread c factor) function = ENNReal.additiveLaws.listSum ((F.slots c).map fun a =>
      ENNReal.mul (factor a) (function (F.insert c a))) := by
  rw [spread, lintegral_listSum, List.map_map]
  exact ENNReal.additiveLaws.listSum_map_congr _ fun a _ => by
    change lintegral (Measure.smul _ _) function = _
    rw [lintegral_smul_measure, lintegral_dirac X _ measurable]

/-- The embedding of a sum of nonnegative reals is the sum of the embeddings. -/
public theorem finite_listSum {ι : Type w} (indices : List ι) (values : ι → NNReal) :
    ENNReal.finite (NNReal.additiveLaws.listSum (indices.map values)) =
      ENNReal.additiveLaws.listSum (indices.map fun index => ENNReal.finite (values index)) :=
  NNReal.additiveLaws.listSum_map_hom ENNReal.additiveLaws ENNReal.finite rfl (fun _ _ => rfl)
    indices values

/-- At a positive total, the shares sum to one. -/
public theorem listSum_share {c : γ} (positive : F.total c ≠ NNReal.zero) :
    ENNReal.additiveLaws.listSum ((F.slots c).map (F.share c)) = ENNReal.one := by
  have scaled : NNReal.additiveLaws.listSum ((F.slots c).map fun a =>
      NNReal.div (F.weight c a) (F.total c)) = NNReal.one := by
    apply NNReal.mul_left_cancel positive
    rw [NNReal.mul_one, NNReal.additiveLaws.listSum_map_hom NNReal.additiveLaws (NNReal.mul _)
      (NNReal.mul_zero _) (NNReal.mul_add _)]
    exact NNReal.additiveLaws.listSum_map_congr _ fun a _ => NNReal.mul_div_cancel _ positive
  change _ = ENNReal.finite NNReal.one
  rw [← scaled, finite_listSum]
  rfl

public theorem draw_isProbability {c : γ} (positive : F.total c ≠ NNReal.zero) :
    Measure.IsProbability (F.draw c) := by
  constructor
  rw [draw, F.spread_apply c _ (Space.univ X)]
  refine (ENNReal.additiveLaws.listSum_map_congr _ fun a _ => ?_).trans (F.listSum_share positive)
  rw [Measure.dirac_apply_of_mem X _ (Space.univ X) trivial, ENNReal.mul_one]

/-- Pointwise: with distinct slots and an insertion injective on them, the draw
puts each slot's share on its insertion. -/
public theorem draw_insert {c : γ} (nodup : (F.slots c).Nodup)
    (injective : ∀ a, a ∈ F.slots c → ∀ b, b ∈ F.slots c →
      F.insert c a = F.insert c b → a = b)
    (singleton : ∀ point, X.Measurable (· = point)) {a : σ} (member : a ∈ F.slots c) :
    F.draw c (· = F.insert c a) = F.share c a := by
  rw [draw, F.spread_apply c _ (singleton _)]
  refine (ENNReal.additiveLaws.listSum_map_eq_single _ a nodup member _
    fun b inside other => ?_).trans ?_
  · rw [Measure.dirac_apply X _ (singleton _),
      ite_eq_right fun same => other (injective b inside a member same), ENNReal.mul_zero]
  · rw [Measure.dirac_apply_of_mem X _ (singleton _) rfl, ENNReal.mul_one]

/-- A sum of nonnegative reals is zero only when every term is. -/
private theorem listSum_eq_zero {ι : Type w} : ∀ (indices : List ι) (values : ι → NNReal),
    NNReal.additiveLaws.listSum (indices.map values) = NNReal.zero →
      ∀ index, index ∈ indices → values index = NNReal.zero
  | [], _, _, _, member => absurd member List.not_mem_nil
  | head :: rest, values, zero, index, member => by
      have split := NNReal.add_eq_zero_iff.mp
        (show NNReal.add (values head) (NNReal.additiveLaws.listSum (rest.map values)) =
          NNReal.zero from zero)
      rcases List.mem_cons.mp member with same | inside
      · exact same ▸ split.1
      · exact listSum_eq_zero rest values split.2 index inside

/-- At a context of total zero every weight is zero. -/
public theorem weight_zero {c : γ} (zero : F.total c = NNReal.zero) :
    ∀ a, a ∈ F.slots c → F.weight c a = NNReal.zero :=
  listSum_eq_zero (F.slots c) (F.weight c) zero

/-- On a valid context, any kernel that agrees with the draw at positive total
moves the context's unnormalized reinsertion to itself. -/
theorem lintegral_mass {move : Kernel X X}
    (agrees : ∀ x, F.total (F.delete x) ≠ NNReal.zero → move x = F.draw (F.delete x))
    {c : γ} (valid : F.Valid c) {set : Set β} (measurable : X.Measurable set) :
    lintegral (F.mass c) (fun x => move x set) = F.mass c set := by
  change lintegral (F.spread c _) _ = F.spread c _ set
  rw [F.lintegral_spread c _ (move.measurable measurable), F.spread_apply c _ measurable]
  by_cases zero : F.total c = NNReal.zero
  · have vanish : ∀ factor : σ → ENNReal,
        ENNReal.additiveLaws.listSum ((F.slots c).map fun a =>
          ENNReal.mul (ENNReal.finite (F.weight c a)) (factor a)) = ENNReal.zero := fun factor =>
      ENNReal.additiveLaws.listSum_map_eq_zero _ _ fun a member => by
        rw [F.weight_zero zero a member]
        exact ENNReal.zero_mul _
    rw [vanish, vanish]
  · have moved : ∀ a, a ∈ F.slots c → move (F.insert c a) set = F.draw c set :=
      fun a member => by
        rw [agrees _ (by rw [F.delete_insert valid a member]; exact zero),
          F.delete_insert valid a member]
    rw [ENNReal.additiveLaws.listSum_map_congr _ fun a member =>
        (congrArg (ENNReal.mul _) (moved a member)).trans (ENNReal.mul_comm _ _),
      ENNReal.semiring.listSum_map_mul_left, ← finite_listSum]
    change ENNReal.mul _ _ = _
    rw [ENNReal.mul_comm, draw, F.spread_apply c _ measurable]
    refine (ENNReal.semiring.listSum_map_mul_left _ _ _).symm.trans
      (ENNReal.additiveLaws.listSum_map_congr _ fun a _ => ?_)
    change ENNReal.mul _ (ENNReal.mul _ _) = _
    rw [← ENNReal.mul_assoc, share, ENNReal.finite_mul_finite,
      show NNReal.additiveLaws.listSum ((F.slots c).map (F.weight c)) = F.total c from rfl,
      NNReal.mul_div_cancel _ zero]

/-- X5, pointwise interface: any kernel that agrees with the site draw at every
point of positive total leaves a target in sum form invariant. -/
public theorem invariant_of_agrees {target : Measure X} {ν : Measure C}
    (sum : target = ν.bind F.mass) (valid : ν.AE F.Valid) (move : Kernel X X)
    (agrees : ∀ x, F.total (F.delete x) ≠ NNReal.zero → move x = F.draw (F.delete x)) :
    target.bind move = target := by
  apply Measure.ext
  intro set measurable
  rw [Measure.bind_apply _ _ measurable, sum,
    Measure.lintegral_bind _ _ (move.measurable measurable),
    Measure.bind_apply _ _ measurable]
  exact lintegral_congr_ae (valid.mono fun c member => F.lintegral_mass agrees member measurable)

/-- X5, sum form: resampling the site from the target's finite disintegration
leaves the target invariant, whatever the move does at total zero. -/
public theorem kernel_invariant {target : Measure X} {ν : Measure C}
    (sum : target = ν.bind F.mass) (valid : ν.AE F.Valid) (fallback : Kernel X X) :
    target.bind (F.kernel fallback) = target :=
  F.invariant_of_agrees sum valid _ fun _ positive => F.kernel_positive fallback positive

/-- The site with each slot's weight multiplied by a local factor. -/
@[expose] public noncomputable def reweight (factor : γ → σ → NNReal) : FiniteSite X C σ :=
  { F with weight := fun c a => NNReal.mul (F.weight c a) (factor c a) }

/-- A density that factors at the site reweights the disintegration: the
weighted target disintegrates over the context law weighted by the outer factor,
with each slot's weight times its local factor. -/
public theorem withDensity_sum {target : Measure X} {ν : Measure C}
    (sum : target = ν.bind F.mass) (valid : ν.AE F.Valid)
    {density : β → ENNReal} (measurable : ENNRealMeasurable X density)
    {outer : γ → ENNReal} {factor : γ → σ → NNReal}
    (factors : ∀ c, F.Valid c → ∀ a ∈ F.slots c,
      density (F.insert c a) = ENNReal.mul (outer c) (ENNReal.finite (factor c a))) :
    target.withDensity density = (ν.withDensity outer).bind (F.reweight factor).mass := by
  apply Measure.ext
  intro set setMeasurable
  have indicator := ENNRealMeasurable.indicator setMeasurable
    (ENNRealMeasurable.constant X ENNReal.one)
  rw [apply_eq_lintegral_indicator _ setMeasurable, lintegral_withDensity _ measurable indicator,
    sum, Measure.lintegral_bind _ _ (ENNRealMeasurable.mul measurable indicator),
    Measure.bind_apply _ _ setMeasurable,
    lintegral_withDensity _ (measurable_of_discrete F.context_discrete _)
      (measurable_of_discrete F.context_discrete _)]
  refine lintegral_congr_ae (valid.mono fun c member => ?_)
  change lintegral (F.spread c _) _ =
    ENNReal.mul (outer c) ((F.reweight factor).spread c (fun a =>
      ENNReal.finite (NNReal.mul (F.weight c a) (factor c a))) set)
  rw [F.lintegral_spread c _ (ENNRealMeasurable.mul measurable indicator),
    (F.reweight factor).spread_apply c _ setMeasurable]
  refine Eq.trans ?_ (ENNReal.semiring.listSum_map_mul_left _ _ _)
  refine ENNReal.additiveLaws.listSum_map_congr _ fun a slot => ?_
  change ENNReal.mul _ (ENNReal.mul (density (F.insert c a)) _) =
    ENNReal.mul (outer c) (ENNReal.mul _ (Measure.dirac X (F.insert c a) set))
  rw [factors c member a slot, ← ENNReal.finite_mul_finite]
  by_cases inside : set (F.insert c a)
  · rw [ennrealIndicator_of_mem inside, Measure.dirac_apply_of_mem X _ setMeasurable inside,
      ENNReal.mul_one, ENNReal.mul_one, ← ENNReal.mul_assoc, ENNReal.mul_comm _ (outer c),
      ENNReal.mul_assoc]
  · rw [ennrealIndicator_of_not_mem inside, Measure.dirac_apply_of_not_mem X _ setMeasurable inside,
      ENNReal.mul_zero, ENNReal.mul_zero, ENNReal.mul_zero, ENNReal.mul_zero]

end FiniteSite

end Problib.Measure.Kernel.Site
