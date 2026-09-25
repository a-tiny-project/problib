module

public import Problib.Measure.Disintegration
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Normalization
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u v
variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- The graph of a measurable return, with its source first. -/
@[expose] public noncomputable def graphJoint (base : Measure source)
    (ret : α → β) (retMeasurable : MeasurableMap source target ret) :
    Measure (Space.product source target) :=
  base.map (fun x => (x, ret x))
    (Space.pair_measurable (MeasurableMap.identity source) retMeasurable)

/-- The graph's second marginal is exactly the return's image measure. -/
public theorem secondMarginal_graphJoint (base : Measure source)
    (ret : α → β) (retMeasurable : MeasurableMap source target ret) :
    secondMarginal (graphJoint base ret retMeasurable) =
      base.map ret retMeasurable := by
  unfold secondMarginal graphJoint
  rw [map_comp base (fun x => (x, ret x)) Prod.snd
    (Space.pair_measurable (MeasurableMap.identity source) retMeasurable)
    (Space.second_measurable source target)]

/-- A graph integral substitutes the return in the second coordinate. -/
public theorem lintegral_graphJoint (base : Measure source)
    (ret : α → β) (retMeasurable : MeasurableMap source target ret)
    {f : α × β → ENNReal}
    (fMeasurable : ENNRealMeasurable (Space.product source target) f) :
    lintegral (graphJoint base ret retMeasurable) f =
      lintegral base (fun x => f (x, ret x)) := by
  unfold graphJoint
  exact lintegral_map base (fun x => (x, ret x))
    (Space.pair_measurable (MeasurableMap.identity source) retMeasurable)
    fMeasurable

/-- Pulling a graph-disintegrated likelihood through the return gives an
output density against the image of the base. -/
public theorem density_pushforward_of_disintegration
    (base : Measure source) (ret : α → β)
    (retMeasurable : MeasurableMap source target ret)
    (selection : Disintegration (graphJoint base ret retMeasurable))
    {likelihood : α → ENNReal}
    (likelihoodMeasurable : ENNRealMeasurable source likelihood) :
    IsDensity ((base.withDensity likelihood).map ret retMeasurable)
      (base.map ret retMeasurable)
      (fun y => lintegral (selection.conditional y) likelihood) := by
  change (base.withDensity likelihood).map ret retMeasurable =
    (base.map ret retMeasurable).withDensity
      (fun y => lintegral (selection.conditional y) likelihood)
  apply Measure.ext
  intro E hE
  -- The same indicator on the graph is integrated in two sampling orders.
  let f : α × β → ENNReal :=
    fun pair => ENNReal.mul (likelihood pair.1)
      (ennrealIndicator E (fun _ => ENNReal.one) pair.2)
  have hf : ENNRealMeasurable (Space.product source target) f := by
    exact (likelihoodMeasurable.comp (Space.first_measurable source target)).mul
      ((ENNRealMeasurable.indicator hE
        (ENNRealMeasurable.constant target ENNReal.one)).comp
        (Space.second_measurable source target))
  have graphReconstruct :
      reverseSemiproduct (secondMarginal (graphJoint base ret retMeasurable))
        selection.conditional selection.conditionalSFinite =
          graphJoint base ret retMeasurable :=
    selection.reconstruction
  have ordered :
      lintegral (graphJoint base ret retMeasurable) f =
        lintegral (base.map ret retMeasurable)
          (fun y => lintegral (selection.conditional y)
            (fun x => f (x, y))) := by
    calc
      lintegral (graphJoint base ret retMeasurable) f =
          lintegral (reverseSemiproduct
            (secondMarginal (graphJoint base ret retMeasurable))
            selection.conditional selection.conditionalSFinite) f :=
        congrArg (fun measure => lintegral measure f) graphReconstruct.symm
      _ = lintegral (secondMarginal (graphJoint base ret retMeasurable))
          (fun y => lintegral (selection.conditional y) (fun x => f (x, y))) :=
        lintegral_reverseSemiproduct _ _ _ hf
      _ = _ := by rw [secondMarginal_graphJoint]
  have graphSide :
      lintegral (graphJoint base ret retMeasurable) f =
        ((base.withDensity likelihood).map ret retMeasurable) E := by
    rw [lintegral_graphJoint base ret retMeasurable hf]
    have regionMeasurable : source.Measurable (Set.preimage ret E) :=
      retMeasurable hE
    have indicatorMeasurable : ENNRealMeasurable source
        (ennrealIndicator (Set.preimage ret E) (fun _ => ENNReal.one)) :=
      ENNRealMeasurable.indicator regionMeasurable
        (ENNRealMeasurable.constant _ _)
    calc
      lintegral base (fun x => f (x, ret x)) =
          lintegral base (fun x => ENNReal.mul (likelihood x)
            (ennrealIndicator (Set.preimage ret E) (fun _ => ENNReal.one) x)) := rfl
      _ = lintegral (base.withDensity likelihood)
          (ennrealIndicator (Set.preimage ret E) (fun _ => ENNReal.one)) :=
        (lintegral_withDensity base likelihoodMeasurable indicatorMeasurable).symm
      _ = (base.withDensity likelihood) (Set.preimage ret E) :=
        (apply_eq_lintegral_indicator _ regionMeasurable).symm
      _ = ((base.withDensity likelihood).map ret retMeasurable) E :=
        (Measure.map_apply _ _ _ hE).symm
  have fiberSide :
      lintegral (base.map ret retMeasurable)
          (fun y => lintegral (selection.conditional y)
            (fun x => f (x, y))) =
        ((base.map ret retMeasurable).withDensity
          (fun y => lintegral (selection.conditional y) likelihood)) E := by
    let h : β → ENNReal := fun y => lintegral (selection.conditional y) likelihood
    have inner (y : β) :
        lintegral (selection.conditional y) (fun x => f (x, y)) =
          ENNReal.mul (ennrealIndicator E (fun _ => ENNReal.one) y) (h y) := by
      calc
        lintegral (selection.conditional y) (fun x => f (x, y)) =
            lintegral (selection.conditional y) (fun x =>
              ENNReal.mul (ennrealIndicator E (fun _ => ENNReal.one) y)
                (likelihood x)) := by
          apply lintegral_congr
          intro x
          exact ENNReal.mul_comm _ _
        _ = _ := lintegral_smul _ _ likelihoodMeasurable
    have indicatorEq :
        (fun y => ENNReal.mul
          (ennrealIndicator E (fun _ => ENNReal.one) y) (h y)) =
          ennrealIndicator E h := by
      funext y
      classical
      by_cases member : E y
      · simp only [ennrealIndicator, ennrealPiecewise, member, ite_true,
          ENNReal.one_mul]
      · simp only [ennrealIndicator, ennrealPiecewise, member, ite_false,
          ENNReal.zero_mul]
    calc
      lintegral (base.map ret retMeasurable)
          (fun y => lintegral (selection.conditional y) (fun x => f (x, y))) =
        lintegral (base.map ret retMeasurable) (fun y =>
          ENNReal.mul (ennrealIndicator E (fun _ => ENNReal.one) y) (h y)) := by
          apply lintegral_congr
          exact inner
      _ = lintegral ((base.map ret retMeasurable).restrict E) h := by
        rw [indicatorEq, lintegral_indicator _ E hE h]
      _ = ((base.map ret retMeasurable).withDensity h) E :=
        ((base.map ret retMeasurable).withDensity_apply h hE).symm
  exact graphSide.symm.trans (ordered.trans fiberSide)

/-- A requested output reference can itself be described by a density. -/
public theorem density_reference_change {μ middle ν : Measure target}
    {p h : β → ENNReal}
    (density : IsDensity μ middle p) (reference : IsDensity middle ν h)
    (hMeasurable : ENNRealMeasurable target h)
    (pMeasurable : ENNRealMeasurable target p) :
    IsDensity μ ν (fun y => ENNReal.mul (h y) (p y)) := by
  change μ = ν.withDensity (fun y => ENNReal.mul (h y) (p y))
  calc
    μ = middle.withDensity p := density
    _ = (ν.withDensity h).withDensity p := by rw [reference]
    _ = ν.withDensity (fun y => ENNReal.mul (h y) (p y)) :=
      ν.withDensity_withDensity hMeasurable pMeasurable

/-- The posterior image density is the conditional likelihood divided by
its exact evidence mass. -/
public theorem density_pushforward_normalized
    (base : Measure source) (ret : α → β)
    (retMeasurable : MeasurableMap source target ret)
    (selection : Disintegration (graphJoint base ret retMeasurable))
    {likelihood : α → ENNReal}
    (likelihoodMeasurable : ENNRealMeasurable source likelihood)
    {Z : NNReal}
    (nonzero : Z ≠ NNReal.zero)
    (total : (base.withDensity likelihood) Set.univ = ENNReal.finite Z) :
    IsDensity
      ((normalize (base.withDensity likelihood)
        (IsNormalizable.of_finite_mass total nonzero)).map ret retMeasurable)
      (base.map ret retMeasurable)
      (fun y => ENNReal.mul
        (ENNReal.finite (NNReal.div NNReal.one Z))
        (lintegral (selection.conditional y) likelihood)) := by
  let defined := IsNormalizable.of_finite_mass total nonzero
  have imageDefined := defined.map ret retMeasurable
  have normalized := density_pushforward_of_disintegration base ret
    retMeasurable selection likelihoodMeasurable
  let h : β → ENNReal := fun y => lintegral (selection.conditional y) likelihood
  have hMeasurable : ENNRealMeasurable target h := by
    exact Kernel.lintegral_measurable_joint selection.conditional
      selection.conditionalSFinite
      (likelihoodMeasurable.comp (Space.second_measurable target source))
  have imageTotal :
      ((base.withDensity likelihood).map ret retMeasurable) Set.univ =
        ENNReal.finite Z := by
    rw [Measure.map_apply _ _ _ target.univ, Set.preimage_univ]
    exact total
  have hTotal : lintegral (base.map ret retMeasurable) h =
      ENNReal.finite Z := by
    calc
      lintegral (base.map ret retMeasurable) h =
          ((base.map ret retMeasurable).withDensity h) Set.univ := by
        rw [(base.map ret retMeasurable).withDensity_apply h target.univ,
          (base.map ret retMeasurable).restrict_univ]
      _ = ENNReal.finite Z := by
        rw [← normalized]
        exact imageTotal
  rw [← normalize_map (base.withDensity likelihood) defined ret retMeasurable]
  have weightedDefined : IsNormalizable
      ((base.map ret retMeasurable).withDensity h) := by
    rw [← normalized]
    exact imageDefined
  calc
    normalize ((base.withDensity likelihood).map ret retMeasurable)
        imageDefined =
      normalize ((base.map ret retMeasurable).withDensity h)
        weightedDefined :=
      normalize_congr normalized imageDefined weightedDefined
    _ = (base.map ret retMeasurable).withDensity
        (fun y => ENNReal.mul (h y)
          (ENNReal.finite (NNReal.div NNReal.one Z))) :=
      (base.map ret retMeasurable).withDensity_normalize
        hMeasurable weightedDefined hTotal
    _ = _ := by
      apply congrArg ((base.map ret retMeasurable).withDensity)
      funext y
      exact ENNReal.mul_comm _ _

end Problib.Measure.Measure

namespace Problib.Measure.Measure

open Problib.Real
open Problib.Real.Construction

universe u v
variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- A checked branch partition with one density equation per inverse branch.
Zero branches beyond the finite range give the finite case. -/
public theorem density_map_of_branches
    (μ : Measure source) (ret : α → β)
    (retMeasurable : MeasurableMap source target ret)
    (ν : Measure target)
    (count : Nat)
    (branchSet : Nat → Set α)
    (branch : Nat → Measure source)
    (inverse : Nat → β → α)
    (branchWeight : Nat → β → ENNReal)
    (branchMeasurable : ∀ n, ENNRealMeasurable target
      (fun y => branchWeight n y))
    (branchSetMeasurable : ∀ n, source.Measurable (branchSet n))
    (branchEq : ∀ n, branch n = μ.restrict (branchSet n))
    (coverage : ∀ x, ∃ n, branchSet n x)
    (disjoint : Set.PairwiseDisjoint branchSet)
    (_beyond : ∀ n, count ≤ n → branchSet n = Set.empty)
    (_inverseLaw : ∀ n x, branchSet n x → inverse n (ret x) = x)
    (branchReference : ∀ n,
      Measure.IsDensity
        ((branch n).map ret retMeasurable) ν (branchWeight n)) :
    Measure.IsDensity (μ.map ret retMeasurable) ν
      (fun y => ENNReal.tsum (fun n => branchWeight n y)) := by
  have union : Set.iUnion branchSet = Set.univ := by
    apply Set.ext
    intro x
    exact ⟨fun _ => True.intro, fun _ => coverage x⟩
  have partition : μ = Measure.sum branch := by
    calc
      μ = μ.restrict (Set.iUnion branchSet) := by rw [union, μ.restrict_univ]
      _ = Measure.sum (fun n => μ.restrict (branchSet n)) :=
        μ.restrict_iUnion branchSet branchSetMeasurable disjoint
      _ = Measure.sum branch := by
        apply congrArg Measure.sum
        funext n
        exact (branchEq n).symm
  change μ.map ret retMeasurable =
    ν.withDensity (fun y => ENNReal.tsum (fun n => branchWeight n y))
  rw [partition, Measure.map_sum]
  rw [ν.withDensity_tsum branchWeight branchMeasurable]
  apply congrArg Measure.sum
  funext n
  exact branchReference n

/-- Translation sends a density to its translated argument against the same
Lebesgue reference. -/
public theorem density_map_translate
    {μ : Measure Real.borel}
    {p : Real.Carrier → ENNReal}
    (pMeasurable : ENNRealMeasurable Real.borel p)
    (density : IsDensity μ Real.volume p)
    (shift : Real.Carrier) :
    IsDensity
      (μ.map (Dedekind.add shift) (Real.translate_measurable shift))
      Real.volume
      (fun y => p (Dedekind.sub y shift)) := by
  rw [density]
  let q : Real.Carrier → ENNReal := fun y => p (Dedekind.sub y shift)
  have qMeasurable : ENNRealMeasurable Real.borel q :=
    pMeasurable.comp (Real.measurable_sub
      (MeasurableMap.identity Real.borel)
      (MeasurableMap.constant Real.borel Real.borel shift))
  have factor : (fun x => q (Dedekind.add shift x)) = p := by
    funext x
    exact congrArg p (Dedekind.add_sub_self shift x)
  have moved := Measure.map_withDensity Real.volume (Dedekind.add shift)
    (Real.translate_measurable shift) qMeasurable
  change (Real.volume.withDensity p).map (Dedekind.add shift)
    (Real.translate_measurable shift) = Real.volume.withDensity q
  simpa only [factor, Real.map_volume_translate] using moved

end Problib.Measure.Measure
