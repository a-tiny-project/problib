module

public import Problib.Measure.Exchangeable.View
public import Problib.Measure.Exchangeable.Sampled
public import Problib.Measure.Kernel.Product.Density
public import Problib.Measure.Kernel.Product.AlmostEverywhere
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Additive.Counting
public import Problib.Measure.Additive.Atom
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# The density of a sampled urn's history

A statistic reached with positive chain mass from a valid statistic is valid,
since each predictive along the way is positive (`valid_of_chain`). So under
the chain's density the draw kernel agrees with the density kernel
`base.withDensity (predictive s)` almost everywhere, and each step of the
history law multiplies the density by the next predictive. The law of the
first `n` draws is the `n`-fold power of the base with density the chain
(`law_eq_density`), and it is a probability law (`law_isProbability`).
Against a counting base the power puts mass one on each history, so the mass
a view puts on one value is a sum of the chain over the coded histories with
that view (`view_density_counting`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real

public section

universe u v w

variable {α : Type u} {Y : Space α}

/-- A density-weighted measure is concentrated where its density is positive. -/
theorem ae_withDensity_of_ne_zero {β : Type w} {space : Space β} (measure : Measure space)
    {density : β → ENNReal} (measurable : ENNRealMeasurable space density)
    {predicate : β → Prop} (holds : ∀ x, density x ≠ ENNReal.zero → predicate x) :
    (measure.withDensity density).AE predicate := by
  have zeroMeasurable : space.Measurable fun x => density x = ENNReal.zero :=
    ENNRealMeasurable.eq_set measurable (ENNRealMeasurable.constant space ENNReal.zero)
  apply Measure.NullSet.mono (right := fun x => density x = ENNReal.zero)
  · change measure.withDensity density _ = ENNReal.zero
    rw [Measure.withDensity_apply_eq_zero_iff measurable zeroMeasurable]
    have empty : Set.inter (fun x => density x = ENNReal.zero)
        (fun x => density x ≠ ENNReal.zero) = Set.empty :=
      Set.ext fun _ => ⟨fun member => member.2 member.1, False.elim⟩
    rw [empty]
    exact measure.empty_apply
  · intro x failing
    by_cases zero : density x = ENNReal.zero
    · exact zero
    · exact False.elim (failing (holds x zero))

namespace Urn

variable {U : Urn.{u, v} Y}

/-- A statistic reached from a valid one with positive chain mass is valid. -/
theorem valid_of_chain (S : U.Sampled) : ∀ {q : U.Stat} (ys : List α), S.Valid q →
    U.chain q ys ≠ ENNReal.zero → S.Valid (U.stat q ys)
  | _, [], valid, _ => valid
  | q, y :: ys, valid, positive => by
      have split : ENNReal.mul (U.predictive q y) (U.chain (U.incorporate q y) ys) ≠
          ENNReal.zero := positive
      have predictive : U.predictive q y ≠ ENNReal.zero :=
        fun zero => split (ENNReal.mul_eq_zero_iff.mpr (Or.inl zero))
      have rest : U.chain (U.incorporate q y) ys ≠ ENNReal.zero :=
        fun zero => split (ENNReal.mul_eq_zero_iff.mpr (Or.inr zero))
      exact valid_of_chain S ys (S.valid_inc valid predictive) rest

/-- The chain mass of a history is measurable in the history. -/
theorem chain_measurable (U : Urn.{u, v} Y) (q : U.Stat) (n : Nat) :
    ENNRealMeasurable (historySpace Y n) (fun ys => U.chain q (toList ys)) := by
  induction n with
  | zero =>
      have equal : (fun ys : Fin 0 → α => U.chain q (toList ys)) = fun _ => ENNReal.one := by
        funext ys
        rw [toList_empty]
        rfl
      rw [equal]
      exact ENNRealMeasurable.constant _ _
  | succ n induction =>
      have equal : (fun ys : Fin (n + 1) → α => U.chain q (toList ys)) =
          fun ys => ENNReal.mul (U.chain q (toList fun index => ys index.castSucc))
            (U.predictive (U.stat q (toList fun index => ys index.castSucc))
              (ys (Fin.last n))) := by
        funext ys
        unfold toList
        rw [List.ofFn_succ_last, chain_snoc]
      rw [equal]
      have initial : MeasurableMap (historySpace Y (n + 1)) (historySpace Y n)
          (fun ys index => ys index.castSucc) :=
        Space.pi_reindex (fun _ => Y) Fin.castSucc
      have previous : MeasurableMap (historySpace Y (n + 1)) U.statSpace
          (fun ys => U.stat q (toList fun index => ys index.castSucc)) :=
        MeasurableMap.comp (before := fun (ys : Fin (n + 1) → α) index => ys index.castSucc)
          (U.stat_measurable q n) initial
      have last : MeasurableMap (historySpace Y (n + 1)) Y (fun ys => ys (Fin.last n)) :=
        Space.coordinate_measurable (fun _ => Y) (Fin.last n)
      have paired : MeasurableMap (historySpace Y (n + 1)) (Space.product U.statSpace Y)
          (fun ys => (U.stat q (toList fun index => ys index.castSucc), ys (Fin.last n))) :=
        Space.pair_measurable previous last
      have chained : ENNRealMeasurable (historySpace Y (n + 1))
          (fun ys => U.chain q (toList fun index => ys index.castSucc)) :=
        ENNRealMeasurable.comp (before := fun (ys : Fin (n + 1) → α) index => ys index.castSucc)
          induction initial
      have predicted : ENNRealMeasurable (historySpace Y (n + 1))
          (fun ys => U.predictive (U.stat q (toList fun index => ys index.castSucc))
            (ys (Fin.last n))) :=
        ENNRealMeasurable.comp (before := fun (ys : Fin (n + 1) → α) =>
            (U.stat q (toList fun index => ys index.castSucc), ys (Fin.last n)))
          U.predictive_measurable paired
      exact ENNRealMeasurable.mul chained predicted

/-- The predictive at the statistic of a history is jointly measurable. -/
theorem history_predictive_measurable (U : Urn.{u, v} Y) (q : U.Stat) (n : Nat) :
    ENNRealMeasurable (Space.product (historySpace Y n) Y)
      (fun pair => U.predictive (U.stat q (toList pair.1)) pair.2) := by
  have statistic : MeasurableMap (Space.product (historySpace Y n) Y) U.statSpace
      (fun pair => U.stat q (toList pair.1)) :=
    MeasurableMap.comp (before := (Prod.fst : (Fin n → α) × α → Fin n → α))
      (U.stat_measurable q n) (Space.first_measurable (historySpace Y n) Y)
  have paired : MeasurableMap (Space.product (historySpace Y n) Y)
      (Space.product U.statSpace Y) (fun pair => (U.stat q (toList pair.1), pair.2)) :=
    Space.pair_measurable statistic (Space.second_measurable (historySpace Y n) Y)
  exact ENNRealMeasurable.comp
    (before := fun (pair : (Fin n → α) × α) => (U.stat q (toList pair.1), pair.2))
    U.predictive_measurable paired

/-- The density kernel at the statistic of a history: the base with density
the predictive there. -/
@[expose] noncomputable def densityKernel (U : Urn.{u, v} Y) (S : U.Sampled) (q : U.Stat)
    (n : Nat) : Kernel (historySpace Y n) Y :=
  (Kernel.const (historySpace Y n) S.base).withDensity
    (Kernel.IsSFinite.const (historySpace Y n) S.baseFinite)
    (fun ys y => U.predictive (U.stat q (toList ys)) y)
    (history_predictive_measurable U q n)

/-- The density kernel is s-finite. -/
noncomputable def densityKernel_finite (U : Urn.{u, v} Y) (S : U.Sampled) (q : U.Stat)
    (n : Nat) : Kernel.IsSFinite (densityKernel U S q n) :=
  Kernel.IsSFinite.withDensity (Kernel.IsSFinite.const (historySpace Y n) S.baseFinite)
    (fun ys y => U.predictive (U.stat q (toList ys)) y) (history_predictive_measurable U q n)

/-- The law of the first `n` draws from a valid statistic is the `n`-fold power
of the base with the chain as its density. -/
theorem law_eq_density (S : U.Sampled) {q : U.Stat} (valid : S.Valid q) : ∀ n : Nat,
    U.law S q n = (power S.base S.baseFinite n).withDensity (fun ys => U.chain q (toList ys))
  | 0 => by
      have one : (fun ys : Fin 0 → α => U.chain q (toList ys)) = fun _ => ENNReal.one := by
        funext ys
        rw [toList_empty]
        rfl
      rw [one, Measure.withDensity_one]
      rfl
  | n + 1 => by
      rw [law_succ, law_eq_density S valid n]
      have swap :
          Measure.semiproduct
              ((power S.base S.baseFinite n).withDensity fun ys => U.chain q (toList ys))
              (U.historyKernel S q n) (S.kernelFinite.precomp _ (U.stat_measurable q n)) =
            Measure.semiproduct
              ((power S.base S.baseFinite n).withDensity fun ys => U.chain q (toList ys))
              (densityKernel U S q n) (densityKernel_finite U S q n) := by
        apply Measure.semiproduct_congr_ae
        apply ae_withDensity_of_ne_zero _ (U.chain_measurable q n)
        intro ys positive
        show S.kernel (U.stat q (toList ys)) =
          S.base.withDensity (fun y => U.predictive (U.stat q (toList ys)) y)
        exact S.kernel_eq (valid_of_chain S _ valid positive)
      rw [swap, Measure.semiproduct_withDensity_prod _ (U.chain_measurable q n) S.base
        S.baseFinite (densityKernel U S q n) (densityKernel_finite U S q n)
        (kernelDensity := fun pair => U.predictive (U.stat q (toList pair.1)) pair.2)
        (history_predictive_measurable U q n) (fun _ => rfl)]
      have density : (fun pair : (Fin n → α) × α =>
          ENNReal.mul (U.predictive (U.stat q (toList pair.1)) pair.2)
            (U.chain q (toList pair.1))) =
          fun pair => U.chain q (toList (snoc pair.1 pair.2)) := by
        funext pair
        rw [toList_snoc, chain_snoc, ENNReal.mul_comm]
      rw [density, Measure.map_withDensity _ _ (snoc_measurable Y n)
        (U.chain_measurable q (n + 1))]
      rfl

/-- Under the law of the first `n` draws from a valid statistic, the statistic
of the history is almost surely valid. -/
theorem law_valid (S : U.Sampled) {q : U.Stat} (valid : S.Valid q) (n : Nat) :
    (U.law S q n).AE fun ys => S.Valid (U.stat q (toList ys)) := by
  rw [law_eq_density S valid n]
  exact ae_withDensity_of_ne_zero _ (U.chain_measurable q n)
    fun ys positive => valid_of_chain S _ valid positive

/-- The law of the first `n` draws from a valid statistic is a probability law. -/
theorem law_isProbability (S : U.Sampled) {q : U.Stat} (valid : S.Valid q) :
    ∀ n : Nat, Measure.IsProbability (U.law S q n)
  | 0 => Measure.IsProbability.dirac _ _
  | n + 1 => by
      rw [law_succ]
      apply Measure.IsProbability.map
      constructor
      refine (Measure.semiproduct_apply (U.law S q n) (U.historyKernel S q n)
        (S.kernelFinite.precomp _ (U.stat_measurable q n))
        (Space.product (historySpace Y n) Y).univ).trans ?_
      have total : (U.law S q n).AEEq
          (fun ys => U.historyKernel S q n ys (Set.preimage (fun y => (ys, y)) Set.univ))
          (fun _ => ENNReal.one) :=
        Measure.AE.mono (law_valid S valid n) fun ys statValid =>
          (S.markov statValid).univ_eq_one
      rw [Measure.lintegral_congr_ae total, Measure.lintegral_const,
        (law_isProbability S valid n).univ_eq_one, ENNReal.one_mul]

/-- Every view of the history law from the initial statistic is the view of the
chain-weighted power of the base. -/
theorem view_density (S : U.Sampled) (W : View.{u, w} Y) (n : Nat) :
    (U.law S U.init n).map (W.view n) (W.view_measurable n) =
      ((power S.base S.baseFinite n).withDensity fun ys => U.chain U.init (toList ys)).map
        (W.view n) (W.view_measurable n) := by
  rw [law_eq_density S S.valid_init n]

section Counting

open Problib.Countable.Pair

/-- The history of naturals coded by a natural number, when there is one. -/
@[expose] noncomputable def decodeHistory (n code : Nat) : Option (Fin n → Nat) :=
  @dite _ (∃ ys, encodeTuple n ys = code) (Classical.propDecidable _)
    (fun coded => some (Classical.choose coded)) (fun _ => none)

theorem decodeHistory_encode (n : Nat) (ys : Fin n → Nat) :
    decodeHistory n (encodeTuple n ys) = some ys := by
  unfold decodeHistory
  split
  · next coded => exact congrArg some (encodeTuple_injective n (Classical.choose_spec coded))
  · next missing => exact absurd ⟨ys, rfl⟩ missing

theorem encode_of_decodeHistory {n code : Nat} {ys : Fin n → Nat}
    (decoded : decodeHistory n code = some ys) : encodeTuple n ys = code := by
  unfold decodeHistory at decoded
  split at decoded
  · next coded =>
      rw [← Option.some.inj decoded]
      exact Classical.choose_spec coded
  · cases decoded

/-- Each history of naturals has mass one under the power of a base with unit
atoms. -/
theorem power_singleton (base : Measure (Space.discrete Nat)) (finite : Measure.SFinite base)
    (atoms : ∀ a, base (Set.singleton a) = ENNReal.one) :
    ∀ (n : Nat) (ys : Fin n → Nat), power base finite n (Set.singleton ys) = ENNReal.one
  | 0, ys => by
      rw [power_zero]
      exact Measure.dirac_apply_of_mem _ _ (historySpace_nat_measurable 0 _)
        (funext fun index => index.elim0)
  | n + 1, ys => by
      rw [power_succ, Measure.map_apply _ _ _ (historySpace_nat_measurable (n + 1) _)]
      have split : Set.preimage (fun pair : (Fin n → Nat) × Nat => snoc pair.1 pair.2)
          (Set.singleton ys) = Set.product (Set.singleton fun index => ys index.castSucc)
            (Set.singleton (ys (Fin.last n))) := by
        apply Set.ext
        intro pair
        constructor
        · intro equal
          change snoc pair.1 pair.2 = ys at equal
          subst equal
          exact ⟨funext fun index => (snoc_castSucc _ _ index).symm, (snoc_last _ _).symm⟩
        · intro member
          have first : pair.1 = fun index => ys index.castSucc := member.1
          have second : pair.2 = ys (Fin.last n) := member.2
          change snoc pair.1 pair.2 = ys
          rw [first, second, snoc_init_last]
      rw [split, Measure.prod_apply_product _ _ _ (historySpace_nat_measurable n _) True.intro,
        power_singleton base finite atoms n, atoms, ENNReal.one_mul]

/-- Integrating against the power of a base with unit atoms sums over the
coded histories. -/
theorem power_lintegral (base : Measure (Space.discrete Nat)) (finite : Measure.SFinite base)
    (atoms : ∀ a, base (Set.singleton a) = ENNReal.one) (n : Nat)
    (integrand : (Fin n → Nat) → ENNReal) :
    Measure.lintegral (power base finite n) integrand =
      ENNReal.tsum fun code => match decodeHistory n code with
        | none => ENNReal.zero
        | some ys => integrand ys := by
  have sum : power base finite n = Measure.sum fun code => match decodeHistory n code with
      | none => Measure.zero _
      | some ys => Measure.dirac (historySpace (Space.discrete Nat) n) ys := by
    apply Measure.ext_of_atoms (encodeTuple n) (encodeTuple_injective n)
      (fun _ => historySpace_nat_measurable n _)
    intro ys
    rw [power_singleton base finite atoms n ys,
      Measure.sum_apply _ (historySpace_nat_measurable n _),
      ENNReal.tsum_eq_of_at_most_one_nonzero _ (encodeTuple n ys), decodeHistory_encode]
    · change ENNReal.one =
        Measure.dirac (historySpace (Space.discrete Nat) n) ys (Set.singleton ys)
      exact (Measure.dirac_apply_of_mem _ ys (set := Set.singleton ys)
        (historySpace_nat_measurable n _) rfl).symm
    · intro code different
      cases decoded : decodeHistory n code with
      | none => exact Measure.zero_apply _
      | some other =>
          apply Measure.dirac_apply_of_not_mem _ _ (historySpace_nat_measurable n _)
          intro equal
          change other = ys at equal
          subst other
          exact different (encode_of_decodeHistory decoded).symm
  rw [sum, Measure.lintegral_sum]
  apply ENNReal.tsum_congr
  intro code
  cases decodeHistory n code with
  | none => exact Measure.lintegral_zero_measure _
  | some ys =>
      exact Measure.lintegral_dirac_of_measurable_singleton _ _ _
        (historySpace_nat_measurable n _)

/-- The chain mass of the coded history when its view is `v`, and zero
otherwise. -/
@[expose] noncomputable def fiberMass (U : Urn.{0, v} (Space.discrete Nat))
    (W : View.{0, w} (Space.discrete Nat)) (n : Nat) (value : W.V n) (code : Nat) : ENNReal :=
  match decodeHistory n code with
  | none => ENNReal.zero
  | some ys => ennrealIndicator (fun ys => W.view n ys = value)
      (fun ys => U.chain U.init (toList ys)) ys

/-- Against a counting base, the mass a view of the history law puts on one
value is the sum of the chain over the coded histories with that view. -/
theorem view_density_counting {U : Urn.{0, v} (Space.discrete Nat)} (S : U.Sampled)
    (counting : S.base = Measure.counting) (W : View.{0, w} (Space.discrete Nat)) (n : Nat)
    (value : W.V n) (single : (W.space n).Measurable (· = value)) :
    (U.law S U.init n).map (W.view n) (W.view_measurable n) (· = value) =
      ENNReal.tsum (fun code => fiberMass U W n value code) := by
  have atoms : ∀ a, S.base (Set.singleton a) = ENNReal.one := fun a => by
    rw [counting]
    exact Measure.counting_singleton a
  rw [Measure.map_apply _ _ _ single, law_eq_density S S.valid_init n,
    Measure.withDensity_apply _ _ (historySpace_nat_measurable n _),
    ← Measure.lintegral_indicator _ _ (historySpace_nat_measurable n _),
    power_lintegral S.base S.baseFinite atoms n]
  rfl

end Counting

end Urn

end

end Problib.Measure.Exchangeable
