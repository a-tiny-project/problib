module

public import Problib.Measure.Kernel.RadonNikodym.Basic
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Iteration
public import Problib.Measure.Kernel.Composition.Bind
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Normalization

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v w
variable {α : Type u} {τ : Type v} {β : Type w}
  {source : Space α} {middle : Space τ} {target : Space β}

/-- A deterministic return against itself has unit density. -/
public noncomputable def densityReturn (v : α → β)
    (vMeasurable : MeasurableMap source target v) :
    RadonNikodymDerivative (deterministic v vMeasurable)
      (deterministic v vMeasurable) :=
  RadonNikodymDerivative.identity _

/-- The atomic variant records the reference's charge of the returned atom. -/
@[expose] public noncomputable def atomReciprocal : ENNReal → ENNReal
  | .finite weight => .finite (NNReal.div NNReal.one weight)
  | .top => ENNReal.zero

private theorem atomReciprocal_mul {weight : ENNReal}
    (finite : ENNReal.Finite weight) (nonzero : weight ≠ ENNReal.zero) :
    ENNReal.mul (atomReciprocal weight) weight = ENNReal.one := by
  rcases ENNReal.exists_finite_of_finite finite with ⟨value, rfl⟩
  have valueNonzero : value ≠ NNReal.zero := by
    intro equal
    exact nonzero (congrArg ENNReal.finite equal)
  change ENNReal.finite (NNReal.mul (NNReal.div NNReal.one value) value) =
    ENNReal.finite NNReal.one
  exact congrArg ENNReal.finite (NNReal.div_mul_cancel NNReal.one valueNonzero)

public noncomputable def densityReturnAtom
    (v : α → β) (vMeasurable : MeasurableMap source target v)
    (reference : Kernel source target)
    (atom : α → ENNReal)
    (atomEq : ∀ input, reference input (Set.singleton (v input)) = atom input)
    (atomPositive : ∀ input, atom input ≠ ENNReal.zero)
    (atomFinite : ∀ input, ENNReal.Finite (atom input))
    (singletonMeasurable : ∀ output, target.Measurable (Set.singleton output))
    (jointMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => ennrealIndicator
        (fun p : α × β => p.2 = v p.1)
        (fun p => atomReciprocal (atom p.1)) pair)) :
    RadonNikodymDerivative (deterministic v vMeasurable) reference := by
  refine ⟨fun input output => ennrealIndicator
      (Set.singleton (v input))
      (fun _ => atomReciprocal (atom input)) output,
    jointMeasurable, ?_⟩
  intro input
  change Measure.dirac target (v input) =
    (reference input).withDensity
      (ennrealIndicator (Set.singleton (v input))
        (fun _ => atomReciprocal (atom input)))
  rw [(reference input).withDensity_indicator _
    (singletonMeasurable (v input)), Measure.withDensity_const]
  apply Measure.ext
  intro E hE
  rw [Measure.dirac_apply target (v input) hE,
    Measure.smul_apply_measurable _ _ hE,
    Measure.restrict_apply _ _ hE]
  classical
  by_cases member : E (v input)
  · have interEq : Set.inter E (Set.singleton (v input)) =
        Set.singleton (v input) := by
      apply Set.ext
      intro value
      constructor
      · intro present
        exact present.2
      · intro present
        subst value
        exact ⟨member, rfl⟩
    rw [if_pos member, interEq, atomEq,
      atomReciprocal_mul (atomFinite input) (atomPositive input)]
  · have interEmpty : Set.inter E (Set.singleton (v input)) =
        Set.empty := by
      apply Set.ext
      intro value
      constructor
      · intro present
        exact False.elim (member (present.2 ▸ present.1))
      · intro present
        exact False.elim present
    rw [if_neg member, interEmpty, (reference input).empty_apply,
      ENNReal.mul_zero]

/-- The exact bind rule reconstructs the marginal by integrating the
continuation density against A. Its common reference is independent of a. -/
public noncomputable def densityBind
    (A : Kernel source middle) (AFinite : IsSFinite A)
    (B : Kernel (Space.product source middle) target)
    (ν : Kernel source target) (νFinite : IsSFinite ν)
    (b : (α × τ) → β → ENNReal)
    (bMeasurable : ENNRealMeasurable
      (Space.product (Space.product source middle) target)
      (fun pair => b pair.1 pair.2))
    (reconstruct : ∀ input, (A input).AE (fun a =>
      Measure.IsDensity (B (input, a)) (ν input) (b (input, a)))) :
    RadonNikodymDerivative ((A.attach AFinite).comp B) ν := by
  let marginalDensity : α → β → ENNReal :=
    fun input y => lintegral (A input) (fun a => b (input, a) y)
  have marginalMeasurable : ENNRealMeasurable
      (Space.product source target)
      (fun pair => marginalDensity pair.1 pair.2) := by
    let pulled := A.precomp Prod.fst (Space.first_measurable source target)
    have pulledFinite : IsSFinite pulled :=
      AFinite.precomp Prod.fst (Space.first_measurable source target)
    let reorder : (α × β) × τ → (α × τ) × β :=
      fun pair => ((pair.1.1, pair.2), pair.1.2)
    have reorderMeasurable : MeasurableMap
        (Space.product (Space.product source target) middle)
        (Space.product (Space.product source middle) target) reorder := by
      apply Space.pair_measurable
      · apply Space.pair_measurable
        · exact MeasurableMap.comp (Space.first_measurable source target)
            (Space.first_measurable (Space.product source target) middle)
        · exact Space.second_measurable (Space.product source target) middle
      · exact MeasurableMap.comp (Space.second_measurable source target)
          (Space.first_measurable (Space.product source target) middle)
    have lifted : ENNRealMeasurable
        (Space.product (Space.product source target) middle)
        (fun pair => b (pair.1.1, pair.2) pair.1.2) := by
      simpa only [reorder] using bMeasurable.comp reorderMeasurable
    have integrated := Kernel.lintegral_measurable_joint pulled pulledFinite
      (function := fun pair a => b (pair.1, a) pair.2) lifted
    change ENNRealMeasurable (Space.product source target)
      (fun pair => lintegral (A pair.1) (fun a => b (pair.1, a) pair.2))
    exact integrated
  refine ⟨marginalDensity, marginalMeasurable, ?_⟩
  intro input
  apply Measure.ext
  intro E hE
  have bInputMeasurable : ENNRealMeasurable (Space.product middle target)
      (fun pair => b (input, pair.1) pair.2) := by
    have sliceMeasurable : MeasurableMap (Space.product middle target)
        (Space.product (Space.product source middle) target)
        (fun pair => ((input, pair.1), pair.2)) :=
      Space.pair_measurable
        (MeasurableMap.comp (Kernel.pair_left_measurable input)
          (Space.first_measurable middle target))
        (Space.second_measurable middle target)
    exact bMeasurable.comp sliceMeasurable
  have aeEqual : (A input).AEEq
      (fun a => B (input, a) E)
      (fun a => ((ν input).withDensity (b (input, a))) E) :=
    (reconstruct input).mono (fun a equal =>
      congrArg (fun measure : Measure target => measure E) equal)
  have bindSide : ((A.attach AFinite).comp B) input E =
      lintegral (A input) (fun a =>
        lintegral ((ν input).restrict E) (b (input, a))) := by
    calc
      ((A.attach AFinite).comp B) input E =
          lintegral ((A.attach AFinite) input) (fun pair => B pair E) :=
        Kernel.comp_apply_measurable _ _ _ hE
      _ = lintegral (A input) (fun a => B (input, a) E) := by
        rw [Kernel.attach_apply,
          lintegral_map _ _ _ (B.measurable hE)]
      _ = lintegral (A input)
          (fun a => ((ν input).withDensity (b (input, a))) E) :=
        lintegral_congr_ae aeEqual
      _ = _ := by
        apply lintegral_congr
        intro a
        exact (ν input).withDensity_apply _ hE
  have tonelli :
      lintegral (A input) (fun a =>
        lintegral ((ν input).restrict E) (b (input, a))) =
      lintegral ((ν input).restrict E) (fun y =>
        lintegral (A input) (fun a => b (input, a) y)) := by
    let νE := (ν input).restrict E
    have νEFinite : Measure.SFinite νE :=
      (νFinite.measure input).restrict hE
    calc
      lintegral (A input) (fun a => lintegral νE (b (input, a))) =
          lintegral (Measure.prod (A input) νE νEFinite)
            (fun pair => b (input, pair.1) pair.2) :=
        (lintegral_prod (A input) νE νEFinite bInputMeasurable).symm
      _ = lintegral νE (fun y =>
          lintegral (A input) (fun a => b (input, a) y)) :=
        lintegral_prod_symm (A input) νE (AFinite.measure input)
          νEFinite bInputMeasurable
  change ((A.attach AFinite).comp B) input E =
    ((ν input).withDensity (marginalDensity input)) E
  rw [bindSide, (ν input).withDensity_apply _ hE]
  exact tonelli

/-- Multiplying an exact density by a measurable output score. -/
public theorem density_score
    {μ ν : Measure target} {p s : β → ENNReal}
    (density : Measure.IsDensity μ ν p)
    (pMeasurable : ENNRealMeasurable target p)
    (sMeasurable : ENNRealMeasurable target s) :
    Measure.IsDensity (μ.withDensity s) ν
      (fun y => ENNReal.mul (p y) (s y)) := by
  change μ.withDensity s = ν.withDensity (fun y => ENNReal.mul (p y) (s y))
  rw [density]
  exact ν.withDensity_withDensity pMeasurable sMeasurable

/-- Normalize with an exact, finite, nonzero evidence mass. -/
public theorem density_normalize
    {μ ν : Measure target} {p : β → ENNReal}
    (density : Measure.IsDensity μ ν p)
    (pMeasurable : ENNRealMeasurable target p)
    (defined : Measure.IsNormalizable μ)
    {Z : NNReal} (total : μ Set.univ = ENNReal.finite Z) :
    Measure.IsDensity (Measure.normalize μ defined) ν
      (fun y => ENNReal.mul (p y)
        (ENNReal.finite (NNReal.div NNReal.one Z))) := by
  have totalIntegral : lintegral ν p = ENNReal.finite Z := by
    rw [density, ν.withDensity_apply p target.univ, ν.restrict_univ] at total
    exact total
  let weightedDefined : Measure.IsNormalizable (ν.withDensity p) :=
    density ▸ defined
  change Measure.normalize μ defined = ν.withDensity _
  calc
    Measure.normalize μ defined =
        Measure.normalize (ν.withDensity p) weightedDefined :=
      Measure.normalize_congr density defined weightedDefined
    _ = _ := ν.withDensity_normalize pMeasurable weightedDefined totalIntegral

/-- A common reference makes countable superposition pointwise in density. -/
public theorem density_superpose
    (ν : Measure target) (μ : Nat → Measure target)
    (p : Nat → β → ENNReal)
    (pMeasurable : ∀ n, ENNRealMeasurable target (p n))
    (reconstruct : ∀ n, Measure.IsDensity (μ n) ν (p n)) :
    Measure.IsDensity (Measure.sum μ) ν
      (fun y => ENNReal.tsum (fun n => p n y)) := by
  change Measure.sum μ = ν.withDensity (fun y => ENNReal.tsum (fun n => p n y))
  rw [ν.withDensity_tsum p pMeasurable]
  apply congrArg Measure.sum
  funext n
  exact reconstruct n

/-- The binary product-density step for a finite memory table. The complete
finite-key rule awaits W1d's canonical `Kernel.finProduct` constructor; the
landing-slice change is under DELTA 01M3ABVCMBBGDH5S4G52DH1YCE. -/
public theorem density_product_two
    {μ₁ ν₁ : Measure middle} {μ₂ ν₂ : Measure target}
    (μ₂Finite : Measure.SFinite μ₂) (ν₂Finite : Measure.SFinite ν₂)
    {p : τ → ENNReal} {q : β → ENNReal}
    (first : Measure.IsDensity μ₁ ν₁ p)
    (second : Measure.IsDensity μ₂ ν₂ q)
    (pMeasurable : ENNRealMeasurable middle p)
    (qMeasurable : ENNRealMeasurable target q) :
    Measure.IsDensity
      (Measure.prod μ₁ μ₂ μ₂Finite)
      (Measure.prod ν₁ ν₂ ν₂Finite)
      (fun pair => ENNReal.mul (p pair.1) (q pair.2)) := by
  cases first
  cases second
  let base := Kernel.const middle ν₂
  let baseFinite := IsSFinite.const middle ν₂Finite
  let qJoint : τ → β → ENNReal := fun _ y => q y
  have qJointMeasurable : ENNRealMeasurable (Space.product middle target)
      (fun pair => qJoint pair.1 pair.2) :=
    qMeasurable.comp (Space.second_measurable middle target)
  have kernelEq : base.withDensity baseFinite qJoint qJointMeasurable =
      Kernel.const middle (ν₂.withDensity q) := by
    apply Kernel.ext
    intro input
    rfl
  change Measure.prod (ν₁.withDensity p) (ν₂.withDensity q) μ₂Finite =
    (Measure.prod ν₁ ν₂ ν₂Finite).withDensity
      (fun pair => ENNReal.mul (p pair.1) (q pair.2))
  calc
    Measure.prod (ν₁.withDensity p) (ν₂.withDensity q) μ₂Finite =
        (ν₁.withDensity p).semiproduct
          (base.withDensity baseFinite qJoint qJointMeasurable)
          (IsSFinite.withDensity baseFinite qJoint qJointMeasurable) := by
      apply Measure.ext
      intro E hE
      rw [Measure.prod_apply _ _ _ hE,
        Measure.semiproduct_apply _ _ _ hE]
      apply lintegral_congr
      intro a
      have equal := congrArg (fun current : Kernel middle target =>
        current a (Set.preimage (fun y => (a, y)) E)) kernelEq
      exact equal.symm
    _ = (ν₁.semiproduct base baseFinite).withDensity
          (fun pair => ENNReal.mul (p pair.1) (qJoint pair.1 pair.2)) :=
      Measure.semiproduct_withDensity ν₁ base baseFinite
        pMeasurable qJointMeasurable
    _ = (Measure.prod ν₁ ν₂ ν₂Finite).withDensity
          (fun pair => ENNReal.mul (p pair.1) (q pair.2)) := rfl

/-- The countable-table rule exposes the RN limit and reconstruction; no
martingale convergence is inferred from the increment densities alone. -/
public structure TableDensityLimit (μ ν : Measure target)
    (p : β → ENNReal) : Prop where
  measurable : ENNRealMeasurable target p
  reconstruct : Measure.IsDensity μ ν p

public theorem density_mem_of_limit {μ ν : Measure target}
    {p : β → ENNReal} (limit : TableDensityLimit μ ν p) :
    Measure.IsDensity μ ν p :=
  limit.reconstruct

private theorem density_comp_const
    (A : Kernel source source) (AFinite : IsSFinite A)
    (R : Kernel source target)
    (ν : Measure target) (νFinite : Measure.SFinite ν)
    (exitReconstruct : RadonNikodymDerivative R (Kernel.const source ν))
    (input : α) :
    Measure.IsDensity ((A.comp R) input) ν
      (fun y => lintegral (A input)
        (fun z => exitReconstruct.density z y)) := by
  let B : Kernel (Space.product source source) target :=
    R.precomp Prod.snd (Space.second_measurable source source)
  let b : (α × α) → β → ENNReal :=
    fun pair y => exitReconstruct.density pair.2 y
  have bMeasurable : ENNRealMeasurable
      (Space.product (Space.product source source) target)
      (fun pair => b pair.1 pair.2) := by
    have reorderMeasurable : MeasurableMap
        (Space.product (Space.product source source) target)
        (Space.product source target)
        (fun pair => (pair.1.2, pair.2)) :=
      Space.pair_measurable
        (MeasurableMap.comp (Space.second_measurable source source)
          (Space.first_measurable (Space.product source source) target))
        (Space.second_measurable (Space.product source source) target)
    exact exitReconstruct.density_measurable.comp reorderMeasurable
  have reconstruct : ∀ input, (A input).AE (fun a =>
      Measure.IsDensity (B (input, a)) ν (b (input, a))) := by
    intro input
    apply Measure.ae_of_forall
    intro a
    exact exitReconstruct.reconstruct a
  let d := densityBind A AFinite B (Kernel.const source ν)
    (IsSFinite.const source νFinite) b bMeasurable reconstruct
  have kernelEq : (A.attach AFinite).comp B = A.comp R := by
    apply Kernel.ext
    intro input
    apply Measure.ext
    intro E hE
    rw [Kernel.comp_apply_measurable (A.attach AFinite) B input hE,
      Kernel.comp_apply_measurable A R input hE,
      Kernel.attach_apply,
      lintegral_map _ _ _ (B.measurable hE)]
    rfl
  rw [← kernelEq]
  change Measure.IsDensity (((A.attach AFinite).comp B) input)
    ((Kernel.const source ν) input) (d.density input)
  exact d.reconstruct input

/-- The loop law is the countable sum of its exit-path densities. -/
public noncomputable def densityLoop
    (Q : Kernel source source) (R : Kernel source target)
    (QFinite : IsSFinite Q)
    (ν : Measure target) (νFinite : Measure.SFinite ν)
    (exitReconstruct : RadonNikodymDerivative R (Kernel.const source ν)) :
    RadonNikodymDerivative (loop Q R) (Kernel.const source ν) := by
  let pathDensity : Nat → α → β → ENNReal :=
    fun n input y => lintegral ((iterate Q n) input)
      (fun z => exitReconstruct.density z y)
  have pathMeasurable : ∀ n, ENNRealMeasurable
      (Space.product source target)
      (fun pair => pathDensity n pair.1 pair.2) := by
    intro n
    let step := iterate Q n
    let pulled := step.precomp Prod.fst
      (Space.first_measurable source target)
    have pulledFinite : IsSFinite pulled :=
      (QFinite.iterate n).precomp Prod.fst
        (Space.first_measurable source target)
    let reorder : (α × β) × α → α × β :=
      fun pair => (pair.2, pair.1.2)
    have reorderMeasurable : MeasurableMap
        (Space.product (Space.product source target) source)
        (Space.product source target) reorder :=
      Space.pair_measurable
        (Space.second_measurable (Space.product source target) source)
        (MeasurableMap.comp (Space.second_measurable source target)
          (Space.first_measurable (Space.product source target) source))
    have lifted : ENNRealMeasurable
        (Space.product (Space.product source target) source)
        (fun pair => exitReconstruct.density pair.2 pair.1.2) := by
      simpa only [reorder] using
        exitReconstruct.density_measurable.comp reorderMeasurable
    have integrated := Kernel.lintegral_measurable_joint pulled pulledFinite
      (function := fun pair z => exitReconstruct.density z pair.2) lifted
    change ENNRealMeasurable (Space.product source target)
      (fun pair => lintegral ((iterate Q n) pair.1)
        (fun z => exitReconstruct.density z pair.2))
    exact integrated
  have pathReconstruct : ∀ n input, Measure.IsDensity
      (((iterate Q n).comp R) input) ν (pathDensity n input) := by
    intro n input
    exact density_comp_const (iterate Q n) (QFinite.iterate n)
      R ν νFinite exitReconstruct input
  refine ⟨fun input y => ENNReal.tsum (fun n => pathDensity n input y),
    ENNRealMeasurable.tsum pathMeasurable, ?_⟩
  intro input
  rw [loop_apply]
  exact density_superpose ν
    (fun n => ((iterate Q n).comp R) input)
    (fun n => pathDensity n input)
    (fun n => jointly_measurable_slice (pathMeasurable n) input)
    (fun n => pathReconstruct n input)

/-- Recursion through increment measures is a countable density sum. -/
public theorem density_recur_of_increments
    (μ ν : Measure target) (increment : Nat → Measure target)
    (incrementDensity : Nat → β → ENNReal)
    (sumEq : μ = Measure.sum increment)
    (measurable : ∀ n, ENNRealMeasurable target (incrementDensity n))
    (reconstruct : ∀ n, Measure.IsDensity (increment n) ν
      (incrementDensity n)) :
    Measure.IsDensity μ ν
      (fun y => ENNReal.tsum (fun n => incrementDensity n y)) := by
  rw [sumEq]
  exact density_superpose ν increment incrementDensity measurable reconstruct

end Problib.Measure.Kernel
