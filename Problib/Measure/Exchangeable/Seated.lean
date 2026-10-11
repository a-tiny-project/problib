module

public import Problib.Measure.Exchangeable.NormalTable
public import Problib.Measure.Exchangeable.Sampled
public import Problib.Measure.Kernel.Composition.Bind.Transport
public import Problib.Measure.Kernel.Product

set_option autoImplicit false

/-!
# Seated urns

A seated observation is a label and a value. An allocation urn `A` over the
labels keeps the seating statistic, and the keyed copy of a likelihood urn `B`
keeps one statistic per label (`Urn.seated`). An observation `(z, y)` moves
`A` by `z` and the keyed `B` by `(z, y)`, and its predictive is `A`'s at `z`
times the keyed `B`'s at `(z, y)`. Each block is its own urn: `A` sees only
the labels, and the keyed `B` sees the labelled values. A sampling kernel of
each block gives one of the seated urn (`Urn.seatedSampled`): draw the label
from `A`'s kernel, then the value from `B`'s kernel at that label's statistic.

`seatedNormal` seats the Normal urn on its count and sum: its statistic is the
allocation's together with each table's count and sum.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind

public section

noncomputable section

universe u v w

variable {α : Type u} {Y : Space α}

namespace Urn

/-- **The seated urn.** An allocation urn over labels and the keyed copy of a
likelihood urn, observing a label and a value. -/
@[expose] def seated (A : Urn.{0, v} (Space.discrete Nat)) (B : Urn.{u, w} Y) :
    Urn.{u, max v w} (Space.product (Space.discrete Nat) Y) where
  Stat := A.Stat × (B.keyed id fun _ _ same => same).Stat
  statSpace := Space.product A.statSpace (B.keyed id fun _ _ same => same).statSpace
  init := (A.init, (B.keyed id fun _ _ same => same).init)
  incorporate := fun s pair =>
    (A.incorporate s.1 pair.1, (B.keyed id fun _ _ same => same).incorporate s.2 pair)
  predictive := fun s pair =>
    ENNReal.mul (A.predictive s.1 pair.1) ((B.keyed id fun _ _ same => same).predictive s.2 pair)
  incorporate_measurable := Space.pair_measurable
    (MeasurableMap.comp A.incorporate_measurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))))
    (MeasurableMap.comp (B.keyed id fun _ _ same => same).incorporate_measurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
        (Space.second_measurable _ _)))
  predictive_measurable := ENNRealMeasurable.mul
    (ENNRealMeasurable.comp A.predictive_measurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))))
    (ENNRealMeasurable.comp (B.keyed id fun _ _ same => same).predictive_measurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
        (Space.second_measurable _ _)))

variable {A : Urn.{0, v} (Space.discrete Nat)} {B : Urn.{u, w} Y}

/-- The likelihood block's statistic at the drawn label. -/
theorem seated_read_measurable :
    MeasurableMap (Space.product (A.seated B).statSpace (Space.discrete Nat)) B.statSpace
      fun pair => pair.1.2 pair.2 := by
  intro set measurable
  exact MeasurableMap.comp (B.keyed_read_measurable id fun _ _ same => same)
    (Space.pair_measurable (Space.second_measurable _ _)
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))) measurable

/-- The label draw beside the seated statistic. -/
@[expose] def seatedFirst (SA : A.Sampled) :
    Kernel (A.seated B).statSpace (Space.product (A.seated B).statSpace (Space.discrete Nat)) :=
  Kernel.attach (SA.kernel.precomp Prod.fst (Space.first_measurable _ _))
    (SA.kernelFinite.precomp _ _)

/-- The value draw at the drawn label, beside the label. -/
@[expose] def seatedSecond (SB : B.Sampled) :
    Kernel (Space.product (A.seated B).statSpace (Space.discrete Nat))
      (Space.product (Space.discrete Nat) Y) :=
  (Kernel.attach (SB.kernel.precomp _ seated_read_measurable) (SB.kernelFinite.precomp _ _)).map
    (fun pair => (pair.1.2, pair.2))
    (Space.pair_measurable
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))

/-- The value block's kernel at each label, for a fixed keyed statistic. -/
@[expose] def labelKernel (SB : B.Sampled) (s : Nat → B.Stat) :
    Kernel (Space.discrete Nat) Y where
  toFun := fun label => SB.kernel (s label)
  measurable := fun _ => ENNRealMeasurable.from_discrete _

@[expose] def labelKernel_finite (SB : B.Sampled) (s : Nat → B.Stat) :
    Kernel.IsSFinite (labelKernel SB s) :=
  SB.kernelFinite.precomp s (MeasurableMap.from_discrete _ s)

/-- One seated draw is the label draw followed by the value draw at its label. -/
theorem seated_kernel_apply (SA : A.Sampled) (SB : B.Sampled) (s : (A.seated B).Stat) :
    (seatedFirst SA).comp (seatedSecond SB) s =
      (SA.kernel s.1).semiproduct (labelKernel SB s.2) (labelKernel_finite SB s.2) := by
  rw [Kernel.comp_apply]
  change ((SA.kernel s.1).map _ _).bind _ = _
  rw [Measure.bind_map]
  unfold Measure.semiproduct
  refine congrArg _ (Kernel.ext fun label => ?_)
  rw [Kernel.precomp_apply, Kernel.attach_apply]
  change (((SB.kernel (s.2 label)).map _ _).map _ _) = _
  rw [Measure.map_comp]
  rfl

/-- Writing a valid statistic at one label keeps every label valid. -/
theorem seated_valid_replace (SB : B.Sampled) {s : Nat → B.Stat} (label : Nat) (y : α)
    (valid : ∀ other, SB.Valid (s other)) (written : SB.Valid (B.incorporate (s label) y)) :
    ∀ other, SB.Valid (Pi.replace s label (B.incorporate (s label) y) other) := by
  intro other
  by_cases same : other = label
  · rw [same, Pi.replace_same]
    exact written
  · rw [Pi.replace_other _ _ same]
    exact valid other

/-- **Sampling the seated urn.** Draw the label from the allocation's kernel,
then the value from the likelihood's kernel at that label's statistic. -/
@[expose] def seatedSampled (SA : A.Sampled) (SB : B.Sampled) : (A.seated B).Sampled where
  Valid := fun s => SA.Valid s.1 ∧ ∀ label, SB.Valid (s.2 label)
  valid_measurable := (Space.product _ _).inter
    (Space.first_measurable _ _ SA.valid_measurable)
    ((Space.product _ _).iInter fun label =>
      MeasurableMap.comp (Space.coordinate_measurable (fun _ : Nat => B.statSpace) label)
        (Space.second_measurable _ _) SB.valid_measurable)
  valid_init := ⟨SA.valid_init, fun _ => SB.valid_init⟩
  valid_inc := fun {s pair} valid nonzero => by
    have factors : A.predictive s.1 pair.1 ≠ ENNReal.zero ∧
        B.predictive (s.2 pair.1) pair.2 ≠ ENNReal.zero :=
      ⟨fun zero => nonzero (ENNReal.mul_eq_zero_iff.mpr (Or.inl zero)),
        fun zero => nonzero (ENNReal.mul_eq_zero_iff.mpr (Or.inr zero))⟩
    exact ⟨SA.valid_inc valid.1 factors.1,
      seated_valid_replace SB pair.1 pair.2 valid.2 (SB.valid_inc (valid.2 pair.1) factors.2)⟩
  base := Measure.prod SA.base SB.base SB.baseFinite
  baseFinite := Measure.SFinite.prod SA.baseFinite SB.baseFinite
  kernel := (seatedFirst SA).comp (seatedSecond SB)
  kernelFinite := Kernel.IsSFinite.comp (Kernel.IsSFinite.attach _)
    (Kernel.IsSFinite.map (Kernel.IsSFinite.attach _) _
      (Space.pair_measurable
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
        (Space.second_measurable _ _)))
  markov := fun {s} valid => by
    rw [seated_kernel_apply]
    exact (SA.markov valid.1).bind _ fun label => by
      rw [Kernel.attach_apply]
      exact (SB.markov (valid.2 label)).map _ _
  kernel_eq := fun {s} valid => by
    rw [seated_kernel_apply, SA.kernel_eq valid.1]
    have weightedMeasurable : ENNRealMeasurable (Space.product (Space.discrete Nat) Y)
        fun pair => B.predictive (s.2 pair.1) pair.2 :=
      ENNRealMeasurable.comp B.predictive_measurable
        (Space.pair_measurable
          (MeasurableMap.comp (MeasurableMap.from_discrete B.statSpace s.2)
            (Space.first_measurable _ _))
          (Space.second_measurable _ _))
    have product := Measure.semiproduct_withDensity SA.base
      (Kernel.const (Space.discrete Nat) SB.base) (Kernel.IsSFinite.const _ SB.baseFinite)
      (p := A.predictive s.1) (ENNRealMeasurable.from_discrete _)
      (q := fun label value => B.predictive (s.2 label) value) weightedMeasurable
    rw [show (Measure.prod SA.base SB.base SB.baseFinite).withDensity ((A.seated B).predictive s) =
        (SA.base.semiproduct (Kernel.const _ SB.base) (Kernel.IsSFinite.const _ SB.baseFinite)).withDensity
          (fun pair => ENNReal.mul (A.predictive s.1 pair.1) (B.predictive (s.2 pair.1) pair.2))
        from rfl, ← product]
    unfold Measure.semiproduct
    refine congrArg _ (Kernel.ext fun label => ?_)
    rw [Kernel.attach_apply, Kernel.attach_apply]
    change (SB.kernel (s.2 label)).map _ _ = (SB.base.withDensity (B.predictive (s.2 label))).map _ _
    rw [SB.kernel_eq (valid.2 label)]

end Urn

/-- **The seated Normal urn.** An allocation urn over labels, and at each label
the Normal urn on its count and sum. -/
@[expose] def seatedNormal (A : Urn.{0, v} (Space.discrete Nat))
    (priorMean priorVar likVar : Carrier) : Urn.{0, v} (Space.product (Space.discrete Nat) borel) :=
  A.seated (normalSummaryUrn priorMean priorVar likVar)

end

end

end Problib.Measure.Exchangeable
