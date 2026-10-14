module

public import Problib.Analysis.PAP.Measurable
public import Problib.Analysis.PAP.Piecewise
public import Problib.Analysis.PAP.Restriction
public import Problib.Measure.Real.Pi
public import Problib.Measure.Kernel.Comap
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Extended.Ratio
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Kernel.Piecewise
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Integral.Lebesgue.Extensionality
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Space.Sigma

/-!
# Trace certificates on Euclidean components

A program's law at an environment is often a sum, over countably many trace
shapes, of weighted Lebesgue measure on the shape's trace coordinates, pushed
forward by a return map. ωPAP's density theorem needs the return map to be PAP
jointly in the environment and the trace, while the weight only needs to be
measurable: a normalizer under a bind, for example, is measurable in the
environment and need not be PAP.

A `Piece` is one shape: its trace dimension, a partial PAP return map on
environment and trace coordinates together, whose c-analytic domain is the
shape's domain, and a jointly measurable weight. A `Certificate` for a kernel
between two Euclidean components is a countable family of pieces whose laws
sum to the kernel at every environment. The rules below build certificates for
the constructs of a first-order probabilistic program: deterministic returns,
uniform draws, scores, countable sums, substitution into the environment,
bind, case splits on a PAP guard, normalization at every input, and sums of
strata whose each step is certified from the earlier ones.

A bind's continuation reads its environment value first, `(value, input)`, as
the kernel semantics' bind does. A sum-valued output is certified one
component at a time, and a bind from it splits over the components. A faithful
consumer needs `Certificate.Regular` beyond the bare invariant.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP.Trace

open Problib.Measure
open Problib.Measure.Real (volumePi volumePiSFinite volumePi_add)
open Problib.Real (ENNReal)
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries (AnalyticVectorOn analytic_on_constant analytic_on_coordinate)

/-- One trace shape: `dimension` Lebesgue coordinates, a return map that is
PAP jointly in environment and trace, and a jointly measurable weight. The
return map's domain is the shape's domain. -/
public structure Piece (environment output : Nat) where
  dimension : Nat
  map : PartialPAP (environment + dimension) output
  weight : carrier (environment + dimension) → ENNReal
  weight_measurable : ENNRealMeasurable (vectorBorel (environment + dimension)) weight

namespace Piece

variable {environment output : Nat}

/-- The weight on the domain, zero off it. -/
@[expose] public noncomputable def joint (piece : Piece environment output) :
    carrier (environment + piece.dimension) → ENNReal :=
  ennrealIndicator piece.map.domain piece.weight

public theorem joint_measurable (piece : Piece environment output) :
    ENNRealMeasurable (vectorBorel (environment + piece.dimension)) piece.joint :=
  ENNRealMeasurable.indicator (c_analytic_measurable piece.map.c_analytic_domain)
    piece.weight_measurable

/-- The weighted trace measure at each environment, as a kernel. -/
@[expose] public noncomputable def traceKernel (piece : Piece environment output) :
    Kernel (vectorBorel environment) (vectorBorel piece.dimension) :=
  (Kernel.const (vectorBorel environment)
      (volumePi piece.dimension : Measure (vectorBorel piece.dimension))).withDensity
    (Kernel.IsSFinite.const _ (volumePiSFinite piece.dimension))
    (fun point trace => piece.joint (pairVector point trace))
    (piece.joint_measurable.comp (pairVector_measurable _ _))

public noncomputable def traceKernel_sfinite (piece : Piece environment output) :
    Kernel.IsSFinite piece.traceKernel :=
  (Kernel.IsSFinite.const _ (volumePiSFinite piece.dimension)).withDensity _
    (piece.joint_measurable.comp (pairVector_measurable _ _))

/-- The piece's law at each environment: weighted Lebesgue measure on the
domain's slice, pushed forward by the return map. -/
@[expose] public noncomputable def kernel (piece : Piece environment output) :
    Kernel (vectorBorel environment) (vectorBorel output) :=
  (piece.traceKernel.attach piece.traceKernel_sfinite).map
    (fun pair => piece.map.totalize (pairVector pair.1 pair.2))
    (MeasurableMap.comp piece.map.totalize_measurable (pairVector_measurable _ _))

public noncomputable def kernel_sfinite (piece : Piece environment output) :
    Kernel.IsSFinite piece.kernel :=
  piece.traceKernel_sfinite.attach.map _
    (MeasurableMap.comp piece.map.totalize_measurable (pairVector_measurable _ _))

/-- A piece's law integrated against an integrand: the weighted integral over
the trace coordinates. -/
@[expose] public noncomputable def traceIntegral (piece : Piece environment output)
    (point : carrier environment) (integrand : carrier output → ENNReal) : ENNReal :=
  lintegral (volumePi piece.dimension : Measure (vectorBorel piece.dimension))
    (fun trace => ENNReal.mul (piece.joint (pairVector point trace))
      (integrand (piece.map.totalize (pairVector point trace))))

private theorem slice_measurable (point : carrier environment) (dimension : Nat) :
    MeasurableMap (vectorBorel dimension) (vectorBorel (environment + dimension))
      (fun trace => pairVector point trace) :=
  MeasurableMap.comp (pairVector_measurable _ _) (Kernel.pair_left_measurable point)

private theorem integrand_measurable (piece : Piece environment output)
    (point : carrier environment) {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand) :
    ENNRealMeasurable (vectorBorel piece.dimension)
      (fun trace => ENNReal.mul (piece.joint (pairVector point trace))
        (integrand (piece.map.totalize (pairVector point trace)))) :=
  ENNRealMeasurable.mul (piece.joint_measurable.comp (slice_measurable point _))
    ((measurable.comp piece.map.totalize_measurable).comp (slice_measurable point _))

/-- Integrating against a piece's law is the piece's trace integral. -/
public theorem lintegral_kernel (piece : Piece environment output)
    (point : carrier environment) {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand) :
    lintegral (piece.kernel point) integrand = piece.traceIntegral point integrand := by
  have composed : ENNRealMeasurable (Space.product (vectorBorel environment)
      (vectorBorel piece.dimension))
      (fun pair => integrand (piece.map.totalize (pairVector pair.1 pair.2))) :=
    measurable.comp (MeasurableMap.comp piece.map.totalize_measurable
      (pairVector_measurable _ _))
  change lintegral (((piece.traceKernel point).map (fun trace => (point, trace))
      (Kernel.pair_left_measurable point)).map _ _) integrand = _
  rw [lintegral_map _ _ _ measurable, lintegral_map _ _ _ composed]
  change lintegral ((volumePi piece.dimension : Measure (vectorBorel piece.dimension)).withDensity
      (fun trace => piece.joint (pairVector point trace))) _ = _
  exact lintegral_withDensity _ (piece.joint_measurable.comp (slice_measurable point _))
    ((measurable.comp piece.map.totalize_measurable).comp (slice_measurable point _))

/-- Two weighted integrands agree where their domains agree and, there, so do
their weights and values. -/
public theorem indicator_mul_congr {α β γ : Type} {left : Set α} {right : Set β}
    {leftWeight : α → ENNReal} {rightWeight : β → ENNReal}
    {leftMap : α → γ} {rightMap : β → γ} {integrand : γ → ENNReal}
    {leftPoint : α} {rightPoint : β}
    (domain : left leftPoint ↔ right rightPoint)
    (weight : left leftPoint → leftWeight leftPoint = rightWeight rightPoint)
    (value : left leftPoint → leftMap leftPoint = rightMap rightPoint) :
    ENNReal.mul (ennrealIndicator left leftWeight leftPoint) (integrand (leftMap leftPoint)) =
      ENNReal.mul (ennrealIndicator right rightWeight rightPoint)
        (integrand (rightMap rightPoint)) := by
  by_cases member : left leftPoint
  · rw [ennrealIndicator_of_mem member, ennrealIndicator_of_mem (domain.mp member),
      weight member, value member]
  · rw [ennrealIndicator_of_not_mem member,
      ennrealIndicator_of_not_mem (fun other => member (domain.mpr other)),
      ENNReal.zero_mul, ENNReal.zero_mul]

/-- A constant map is analytic everywhere. -/
public theorem constant_analytic (source : Nat) {target : Nat} (value : carrier target) :
    AnalyticVectorOn (Set.univ : Set (carrier source)) (fun _ => value) := by
  intro coordinate
  exact analytic_on_constant (is_open_univ source) (value coordinate)

/-- The piece of zero weight, whose law vanishes. -/
@[expose] public noncomputable def empty (environment output : Nat) :
    Piece environment output where
  dimension := 0
  map := PartialPAP.ofAnalytic (fun _ => zeroVector output) (constant_analytic _ _)
  weight := fun _ => ENNReal.zero
  weight_measurable := ENNRealMeasurable.constant _ _

public theorem empty_traceIntegral (point : carrier environment)
    (integrand : carrier output → ENNReal) :
    (empty environment output).traceIntegral point integrand = ENNReal.zero := by
  rw [traceIntegral]
  have vanish : ∀ trace : carrier 0,
      ENNReal.mul ((empty environment output).joint (pairVector point trace))
        (integrand ((empty environment output).map.totalize (pairVector point trace))) =
        ENNReal.zero := by
    intro trace
    have zero : (empty environment output).joint (pairVector point trace) = ENNReal.zero := by
      by_cases member : (empty environment output).map.domain (pairVector point trace)
      · exact ennrealIndicator_of_mem member
      · exact ennrealIndicator_of_not_mem member
    rw [zero, ENNReal.zero_mul]
  exact (lintegral_congr _ vanish).trans (lintegral_zero _)

/-- A piece with no trace coordinates, whose law is a weighted Dirac mass. -/
@[expose] public def atom (map : PartialPAP (environment + 0) output)
    (weight : carrier (environment + 0) → ENNReal)
    (measurable : ENNRealMeasurable (vectorBorel (environment + 0)) weight) :
    Piece environment output :=
  ⟨0, map, weight, measurable⟩

/-- The empty trace. -/
@[expose] public def emptyTrace : carrier 0 := fun index => Fin.elim0 index

public theorem atom_traceIntegral (map : PartialPAP (environment + 0) output)
    (weight : carrier (environment + 0) → ENNReal)
    (measurable : ENNRealMeasurable (vectorBorel (environment + 0)) weight)
    (point : carrier environment) {integrand : carrier output → ENNReal}
    (integrandMeasurable : ENNRealMeasurable (vectorBorel output) integrand) :
    (atom map weight measurable).traceIntegral point integrand =
      ENNReal.mul (ennrealIndicator map.domain weight (pairVector point emptyTrace))
        (integrand (map.totalize (pairVector point emptyTrace))) :=
  lintegral_dirac _ _ ((atom map weight measurable).integrand_measurable point integrandMeasurable)

/-- One piece followed by empty ones. -/
@[expose] public noncomputable def single (piece : Piece environment output) :
    Nat → Piece environment output :=
  fun index => if index = 0 then piece else empty environment output

public theorem tsum_single (piece : Piece environment output) (point : carrier environment)
    (integrand : carrier output → ENNReal) :
    ENNReal.tsum (fun index => (single piece index).traceIntegral point integrand) =
      piece.traceIntegral point integrand := by
  rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ 0 (fun index other => by
    simp only [single, ite_eq_right other]
    exact empty_traceIntegral point integrand)]
  simp only [single, ite_eq_left]

/-- Substitute a total joint PAP map into the environment coordinates and
keep the trace coordinates. -/
@[expose] public noncomputable def lift {source : Nat} (dimension : Nat)
    (substitution : PartialPAP environment source) :
    PartialPAP (environment + dimension) (source + dimension) :=
  ((PartialPAP.ofAnalytic leftVector (leftVector_analytic environment dimension)).comp
    substitution).pair (PartialPAP.ofAnalytic rightVector (rightVector_analytic environment dimension))

public theorem lift_domain {source : Nat} (dimension : Nat)
    {substitution : PartialPAP environment source} (total : ∀ point, substitution.domain point)
    (point : carrier environment) (trace : carrier dimension) :
    (lift dimension substitution).domain (pairVector point trace) :=
  (PartialPAP.pair_domain _ _ _).mpr
    ⟨(PartialPAP.comp_domain _ _ _).mpr ⟨PartialPAP.ofAnalytic_domain _ _ _, by
        rw [PartialPAP.ofAnalytic_totalize, leftVector_pairVector]
        exact total point⟩,
      PartialPAP.ofAnalytic_domain _ _ _⟩

public theorem lift_totalize {source : Nat} (dimension : Nat)
    {substitution : PartialPAP environment source} (total : ∀ point, substitution.domain point)
    (point : carrier environment) (trace : carrier dimension) :
    (lift dimension substitution).totalize (pairVector point trace) =
      pairVector (substitution.totalize point) trace := by
  have member := lift_domain dimension total point trace
  rw [lift, PartialPAP.pair_totalize _ _ member,
    PartialPAP.comp_totalize _ _ ((PartialPAP.pair_domain _ _ _).mp member).1,
    PartialPAP.ofAnalytic_totalize, PartialPAP.ofAnalytic_totalize, leftVector_pairVector,
    rightVector_pairVector]

/-- The piece read at a substituted environment. -/
@[expose] public noncomputable def substitute {source : Nat} (piece : Piece source output)
    (substitution : PartialPAP environment source) : Piece environment output where
  dimension := piece.dimension
  map := (lift piece.dimension substitution).comp piece.map
  weight := fun point => piece.weight ((lift piece.dimension substitution).totalize point)
  weight_measurable := piece.weight_measurable.comp (lift piece.dimension substitution).totalize_measurable

public theorem substitute_traceIntegral {source : Nat} (piece : Piece source output)
    {substitution : PartialPAP environment source} (total : ∀ point, substitution.domain point)
    (point : carrier environment) (integrand : carrier output → ENNReal) :
    (piece.substitute substitution).traceIntegral point integrand =
      piece.traceIntegral (substitution.totalize point) integrand := by
  show lintegral (volumePi piece.dimension : Measure (vectorBorel piece.dimension))
      (fun trace => ENNReal.mul
        (ennrealIndicator ((lift piece.dimension substitution).comp piece.map).domain
          (fun inner => piece.weight ((lift piece.dimension substitution).totalize inner))
          (pairVector point trace))
        (integrand (((lift piece.dimension substitution).comp piece.map).totalize
          (pairVector point trace)))) = _
  apply lintegral_congr
  intro trace
  have value := lift_totalize piece.dimension total point trace
  exact indicator_mul_congr
    (left := ((lift piece.dimension substitution).comp piece.map).domain)
    (right := piece.map.domain)
    (leftPoint := pairVector point trace)
    (rightPoint := pairVector (substitution.totalize point) trace)
    (by
      rw [PartialPAP.comp_domain, value]
      exact ⟨fun both => both.2, fun member => ⟨lift_domain _ total point trace, member⟩⟩)
    (fun _ => by
      change piece.weight ((lift piece.dimension substitution).totalize (pairVector point trace)) = _
      rw [value])
    (fun member => by
      rw [PartialPAP.comp_totalize _ _ member, value])

/-- The piece cut to environments in a c-analytic region. -/
@[expose] public noncomputable def restrict (piece : Piece environment output)
    {region : Set (carrier environment)} (analytic : CAnalytic region) :
    Piece environment output where
  dimension := piece.dimension
  map := piece.map.restrict
    (c_analytic_preimage (is_open_univ _) (leftVector_analytic environment piece.dimension) analytic)
  weight := piece.weight
  weight_measurable := piece.weight_measurable

public theorem restrict_traceIntegral_of_mem (piece : Piece environment output)
    {region : Set (carrier environment)} (analytic : CAnalytic region)
    {point : carrier environment} (member : region point) (integrand : carrier output → ENNReal) :
    (piece.restrict analytic).traceIntegral point integrand =
      piece.traceIntegral point integrand := by
  show lintegral (volumePi piece.dimension : Measure (vectorBorel piece.dimension))
      (fun trace => ENNReal.mul
        (ennrealIndicator (piece.restrict analytic).map.domain piece.weight (pairVector point trace))
        (integrand ((piece.restrict analytic).map.totalize (pairVector point trace)))) = _
  apply lintegral_congr
  intro trace
  exact indicator_mul_congr
    (left := (piece.restrict analytic).map.domain) (right := piece.map.domain)
    (leftPoint := pairVector point trace) (rightPoint := pairVector point trace)
    ((PartialPAP.restrict_domain _ _ _).trans ⟨fun both => both.1, fun inside =>
        ⟨inside, True.intro, (congrArg region (leftVector_pairVector point trace)).mpr member⟩⟩)
    (fun _ => rfl)
    (fun inside => PartialPAP.restrict_totalize _ _ inside)

public theorem restrict_traceIntegral_of_not_mem (piece : Piece environment output)
    {region : Set (carrier environment)} (analytic : CAnalytic region)
    {point : carrier environment} (outside : ¬region point) (integrand : carrier output → ENNReal) :
    (piece.restrict analytic).traceIntegral point integrand = ENNReal.zero := by
  have vanish : ∀ trace : carrier piece.dimension,
      ENNReal.mul ((piece.restrict analytic).joint (pairVector point trace))
        (integrand ((piece.restrict analytic).map.totalize (pairVector point trace))) =
        ENNReal.zero := by
    intro trace
    have zero : (piece.restrict analytic).joint (pairVector point trace) = ENNReal.zero :=
      ennrealIndicator_of_not_mem (fun inside => outside (by
        exact (congrArg region (leftVector_pairVector point trace)).mp
          ((PartialPAP.restrict_domain _ _ _).mp inside).2.2))
    rw [zero, ENNReal.zero_mul]
  exact (lintegral_congr _ vanish).trans (lintegral_zero _)

/-- The piece with its weight scaled by a measurable factor of the
environment. -/
@[expose] public noncomputable def scale (piece : Piece environment output)
    (factor : carrier environment → ENNReal)
    (measurable : ENNRealMeasurable (vectorBorel environment) factor) :
    Piece environment output where
  dimension := piece.dimension
  map := piece.map
  weight := fun point => ENNReal.mul (piece.weight point) (factor (leftVector point))
  weight_measurable := ENNRealMeasurable.mul piece.weight_measurable
    (measurable.comp (leftVector_measurable _ _))

public theorem scale_traceIntegral (piece : Piece environment output)
    {factor : carrier environment → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel environment) factor)
    (point : carrier environment) {integrand : carrier output → ENNReal}
    (integrandMeasurable : ENNRealMeasurable (vectorBorel output) integrand) :
    (piece.scale factor measurable).traceIntegral point integrand =
      ENNReal.mul (factor point) (piece.traceIntegral point integrand) := by
  show lintegral (volumePi piece.dimension : Measure (vectorBorel piece.dimension))
      (fun trace => ENNReal.mul
        (ennrealIndicator piece.map.domain
          (fun inner => ENNReal.mul (piece.weight inner) (factor (leftVector inner)))
          (pairVector point trace))
        (integrand (piece.map.totalize (pairVector point trace)))) = _
  refine Eq.trans ?_ (lintegral_smul _ _ (piece.integrand_measurable point integrandMeasurable))
  apply lintegral_congr
  intro trace
  change _ = ENNReal.mul (factor point)
    (ENNReal.mul (ennrealIndicator piece.map.domain piece.weight (pairVector point trace)) _)
  by_cases member : piece.map.domain (pairVector point trace)
  · rw [ennrealIndicator_of_mem member, ennrealIndicator_of_mem member, leftVector_pairVector,
      ENNReal.mul_comm (piece.weight _) (factor point), ENNReal.mul_assoc]
  · rw [ennrealIndicator_of_not_mem member, ennrealIndicator_of_not_mem member,
      ENNReal.zero_mul, ENNReal.mul_zero]

/-- The middle block of a doubly concatenated vector. -/
@[expose] public def middleVector {first second : Nat} :
    carrier (environment + (first + second)) → carrier first :=
  fun point => leftVector (rightVector point)

/-- The last block of a doubly concatenated vector. -/
@[expose] public def lastVector {first second : Nat} :
    carrier (environment + (first + second)) → carrier second :=
  fun point => rightVector (rightVector point)

public theorem middleVector_analytic (first second : Nat) :
    AnalyticVectorOn (Set.univ : Set (carrier (environment + (first + second))))
      (middleVector (environment := environment) (first := first) (second := second)) := by
  intro coordinate
  exact analytic_on_coordinate (is_open_univ _)
    (Fin.natAdd environment (Fin.castAdd second coordinate))

public theorem lastVector_analytic (first second : Nat) :
    AnalyticVectorOn (Set.univ : Set (carrier (environment + (first + second))))
      (lastVector (environment := environment) (first := first) (second := second)) := by
  intro coordinate
  exact analytic_on_coordinate (is_open_univ _)
    (Fin.natAdd environment (Fin.natAdd first coordinate))

/-- A bind piece's input to the first piece: the environment and the first
trace block. -/
@[expose] public noncomputable def firstInput (first second : Nat) :
    PartialPAP (environment + (first + second)) (environment + first) :=
  (PartialPAP.ofAnalytic leftVector (leftVector_analytic environment (first + second))).pair
    (PartialPAP.ofAnalytic middleVector (middleVector_analytic first second))

public theorem firstInput_domain (first second : Nat) (point : carrier environment)
    (head : carrier first) (tail : carrier second) :
    (firstInput first second).domain (pairVector point (pairVector head tail)) :=
  (PartialPAP.pair_domain _ _ _).mpr
    ⟨PartialPAP.ofAnalytic_domain _ _ _, PartialPAP.ofAnalytic_domain _ _ _⟩

public theorem firstInput_totalize (first second : Nat) (point : carrier environment)
    (head : carrier first) (tail : carrier second) :
    (firstInput first second).totalize (pairVector point (pairVector head tail)) =
      pairVector point head := by
  rw [firstInput, PartialPAP.pair_totalize _ _ (firstInput_domain first second point head tail),
    PartialPAP.ofAnalytic_totalize, PartialPAP.ofAnalytic_totalize, leftVector_pairVector]
  change pairVector point (leftVector (rightVector (pairVector point (pairVector head tail)))) = _
  rw [rightVector_pairVector, leftVector_pairVector]

/-- A bind piece's input to the continuation's piece: the first piece's value
ahead of the environment, then the second trace block. -/
@[expose] public noncomputable def continuationInput {middle : Nat}
    (outer : Piece environment middle) (second : Nat) :
    PartialPAP (environment + (outer.dimension + second)) ((middle + environment) + second) :=
  (((firstInput outer.dimension second).comp outer.map).pair
      (PartialPAP.ofAnalytic leftVector (leftVector_analytic environment (outer.dimension + second)))).pair
    (PartialPAP.ofAnalytic lastVector (lastVector_analytic outer.dimension second))

public theorem continuationInput_domain {middle : Nat} (outer : Piece environment middle)
    {second : Nat} (point : carrier environment) (head : carrier outer.dimension)
    (tail : carrier second) :
    (continuationInput outer second).domain (pairVector point (pairVector head tail)) ↔
      outer.map.domain (pairVector point head) := by
  rw [continuationInput, PartialPAP.pair_domain, PartialPAP.pair_domain, PartialPAP.comp_domain,
    firstInput_totalize]
  exact ⟨fun all => all.1.1.2, fun member =>
    ⟨⟨⟨firstInput_domain _ _ point head tail, member⟩, PartialPAP.ofAnalytic_domain _ _ _⟩,
      PartialPAP.ofAnalytic_domain _ _ _⟩⟩

public theorem continuationInput_totalize {middle : Nat} (outer : Piece environment middle)
    {second : Nat} {point : carrier environment} {head : carrier outer.dimension}
    {tail : carrier second} (member : outer.map.domain (pairVector point head)) :
    (continuationInput outer second).totalize (pairVector point (pairVector head tail)) =
      pairVector (pairVector (outer.map.totalize (pairVector point head)) point) tail := by
  have all := (continuationInput_domain outer point head tail).mpr member
  have front := ((PartialPAP.pair_domain _ _ _).mp all).1
  rw [continuationInput, PartialPAP.pair_totalize _ _ all, PartialPAP.pair_totalize _ _ front,
    PartialPAP.comp_totalize _ _ ((PartialPAP.pair_domain _ _ _).mp front).1,
    firstInput_totalize, PartialPAP.ofAnalytic_totalize, PartialPAP.ofAnalytic_totalize,
    leftVector_pairVector]
  change pairVector (pairVector _ point)
    (rightVector (rightVector (pairVector point (pairVector head tail)))) = _
  rw [rightVector_pairVector, rightVector_pairVector]

/-- The piece of a bind: the first piece's trace, then the continuation
piece's, with the continuation read at the first piece's value. -/
@[expose] public noncomputable def bind {middle : Nat} (outer : Piece environment middle)
    (inner : Piece (middle + environment) output) : Piece environment output where
  dimension := outer.dimension + inner.dimension
  map := (continuationInput outer inner.dimension).comp inner.map
  weight := fun point => ENNReal.mul
    (outer.weight ((firstInput outer.dimension inner.dimension).totalize point))
    (inner.weight ((continuationInput outer inner.dimension).totalize point))
  weight_measurable := ENNRealMeasurable.mul
    (outer.weight_measurable.comp (firstInput outer.dimension inner.dimension).totalize_measurable)
    (inner.weight_measurable.comp (continuationInput outer inner.dimension).totalize_measurable)

/-- A piece's trace integral is measurable in the environment. -/
public theorem traceIntegral_measurable (piece : Piece environment output)
    {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand) :
    ENNRealMeasurable (vectorBorel environment) (fun point => piece.traceIntegral point integrand) := by
  have equal : (fun point => piece.traceIntegral point integrand) =
      fun point => lintegral (piece.kernel point) integrand :=
    funext fun point => (piece.lintegral_kernel point measurable).symm
  rw [equal]
  exact Kernel.lintegral_measurable piece.kernel measurable

private theorem rightSlice_measurable (point : carrier environment) (middle : Nat) :
    MeasurableMap (vectorBorel middle) (vectorBorel (middle + environment))
      (fun value => pairVector value point) :=
  MeasurableMap.comp (pairVector_measurable _ _)
    (Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ point))

/-- A bind piece's integrand at a split trace: the first piece's weight times
the continuation piece's integrand at the first piece's value. -/
private theorem bind_integrand {middle : Nat} (outer : Piece environment middle)
    (inner : Piece (middle + environment) output) (point : carrier environment)
    (integrand : carrier output → ENNReal) (head : carrier outer.dimension)
    (tail : carrier inner.dimension) :
    ENNReal.mul ((outer.bind inner).joint (pairVector point (pairVector head tail)))
        (integrand ((outer.bind inner).map.totalize (pairVector point (pairVector head tail)))) =
      ENNReal.mul (outer.joint (pairVector point head))
        (ENNReal.mul (inner.joint (pairVector (pairVector
            (outer.map.totalize (pairVector point head)) point) tail))
          (integrand (inner.map.totalize (pairVector (pairVector
            (outer.map.totalize (pairVector point head)) point) tail)))) := by
  change ENNReal.mul (ennrealIndicator ((continuationInput outer inner.dimension).comp inner.map).domain
      (fun inner' => ENNReal.mul
        (outer.weight ((firstInput outer.dimension inner.dimension).totalize inner'))
        (inner.weight ((continuationInput outer inner.dimension).totalize inner')))
      (pairVector point (pairVector head tail)))
    (integrand (((continuationInput outer inner.dimension).comp inner.map).totalize
      (pairVector point (pairVector head tail)))) =
    ENNReal.mul (ennrealIndicator outer.map.domain outer.weight (pairVector point head))
      (ENNReal.mul (ennrealIndicator inner.map.domain inner.weight _) _)
  by_cases first : outer.map.domain (pairVector point head)
  · have value := continuationInput_totalize outer (tail := tail) first
    rw [ennrealIndicator_of_mem first]
    by_cases second : inner.map.domain
        (pairVector (pairVector (outer.map.totalize (pairVector point head)) point) tail)
    · have both : ((continuationInput outer inner.dimension).comp inner.map).domain
          (pairVector point (pairVector head tail)) :=
        (PartialPAP.comp_domain _ _ _).mpr
          ⟨(continuationInput_domain outer point head tail).mpr first, by rw [value]; exact second⟩
      rw [ennrealIndicator_of_mem both, ennrealIndicator_of_mem second,
        PartialPAP.comp_totalize _ _ both, value, firstInput_totalize, ENNReal.mul_assoc]
    · have neither : ¬((continuationInput outer inner.dimension).comp inner.map).domain
          (pairVector point (pairVector head tail)) := fun both => second (by
        have later := ((PartialPAP.comp_domain _ _ _).mp both).2
        rw [value] at later
        exact later)
      rw [ennrealIndicator_of_not_mem neither, ennrealIndicator_of_not_mem second,
        ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.mul_zero]
  · have neither : ¬((continuationInput outer inner.dimension).comp inner.map).domain
        (pairVector point (pairVector head tail)) := fun both =>
      first ((continuationInput_domain outer point head tail).mp
        ((PartialPAP.comp_domain _ _ _).mp both).1)
    rw [ennrealIndicator_of_not_mem neither, ennrealIndicator_of_not_mem first,
      ENNReal.zero_mul, ENNReal.zero_mul]

/-- A bind piece's trace integral integrates the continuation piece's trace
integral, at the first piece's value, against the first piece's weighted
trace. -/
public theorem bind_traceIntegral {middle : Nat} (outer : Piece environment middle)
    (inner : Piece (middle + environment) output) (point : carrier environment)
    {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand) :
    (outer.bind inner).traceIntegral point integrand =
      lintegral (volumePi outer.dimension : Measure (vectorBorel outer.dimension))
        (fun head => ENNReal.mul (outer.joint (pairVector point head))
          (inner.traceIntegral
            (pairVector (outer.map.totalize (pairVector point head)) point) integrand)) := by
  have whole := (outer.bind inner).integrand_measurable point measurable
  have split : ENNRealMeasurable
      (Space.product (vectorBorel outer.dimension) (vectorBorel inner.dimension))
      (fun pair => ENNReal.mul ((outer.bind inner).joint (pairVector point (pairVector pair.1 pair.2)))
        (integrand ((outer.bind inner).map.totalize (pairVector point (pairVector pair.1 pair.2))))) :=
    whole.comp (pairVector_measurable _ _)
  change lintegral (volumePi (outer.dimension + inner.dimension) :
      Measure (vectorBorel (outer.dimension + inner.dimension))) _ = _
  rw [volumePi_add]
  refine (lintegral_map _ _ _ whole).trans ?_
  refine (lintegral_prod _ _ _ split).trans ?_
  apply lintegral_congr
  intro head
  refine Eq.trans ?_ (lintegral_smul _ _ (inner.integrand_measurable _ measurable))
  apply lintegral_congr
  intro tail
  exact bind_integrand outer inner point integrand head tail

/-- A first piece's trace integral of a sum over continuation pieces is the sum
of the bind pieces' trace integrals. -/
public theorem traceIntegral_bind_tsum {middle : Nat} (outer : Piece environment middle)
    (inners : Nat → Piece (middle + environment) output) (point : carrier environment)
    {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand)
    {continued : carrier (middle + environment) → ENNReal}
    (expansion : ∀ value, continued value =
      ENNReal.tsum (fun index => (inners index).traceIntegral value integrand)) :
    outer.traceIntegral point (fun value => continued (pairVector value point)) =
      ENNReal.tsum (fun index => (outer.bind (inners index)).traceIntegral point integrand) := by
  have argument : MeasurableMap (vectorBorel outer.dimension) (vectorBorel (middle + environment))
      (fun head => pairVector (outer.map.totalize (pairVector point head)) point) :=
    MeasurableMap.comp (rightSlice_measurable point middle)
      (MeasurableMap.comp outer.map.totalize_measurable (slice_measurable point _))
  rw [traceIntegral]
  refine Eq.trans ?_ (ENNReal.tsum_congr (fun index =>
    (outer.bind_traceIntegral (inners index) point measurable).symm))
  refine Eq.trans ?_ (lintegral_tsum _ _ (fun index => ENNRealMeasurable.mul
    (outer.joint_measurable.comp (slice_measurable point _))
    (((inners index).traceIntegral_measurable measurable).comp argument)))
  apply lintegral_congr
  intro head
  rw [expansion, ENNReal.tsum_mul_left]

end Piece

/-- C8's joint invariant on one Euclidean component of the environment and
of the output: the kernel is the sum of countably many pieces' laws at every
environment. -/
public structure Certificate {environment output : Nat}
    (law : Kernel (vectorBorel environment) (vectorBorel output)) where
  pieces : Nat → Piece environment output
  law_eq : ∀ point, law point = Measure.sum (fun index => (pieces index).kernel point)

namespace Certificate

variable {environment output : Nat}
  {law : Kernel (vectorBorel environment) (vectorBorel output)}

/-- A certified kernel is the sum of its pieces' kernels. -/
public theorem eq_sum (certificate : Certificate law) :
    law = Kernel.sum (fun index => (certificate.pieces index).kernel) := by
  apply Kernel.ext
  intro point
  rw [certificate.law_eq point, Kernel.sum_apply]

/-- A certified kernel is s-finite, whatever its weights. -/
public noncomputable def sfinite (certificate : Certificate law) : Kernel.IsSFinite law :=
  certificate.eq_sum ▸ Kernel.IsSFinite.sum _ (fun index => (certificate.pieces index).kernel_sfinite)

/-- Integrating against a certified law sums the pieces' trace integrals. -/
public theorem lintegral (certificate : Certificate law) (point : carrier environment)
    {integrand : carrier output → ENNReal}
    (measurable : ENNRealMeasurable (vectorBorel output) integrand) :
    Problib.Measure.lintegral (law point) integrand =
      ENNReal.tsum (fun index =>
        (certificate.pieces index).traceIntegral point integrand) := by
  rw [certificate.law_eq point, lintegral_sum_measure]
  exact ENNReal.tsum_congr (fun index =>
    (certificate.pieces index).lintegral_kernel point measurable)

/-- Pieces certify a kernel whose integrals are the sums of their trace
integrals. Every rule below is proved in this form. -/
public def ofLintegral (pieces : Nat → Piece environment output)
    (integral : ∀ point {integrand : carrier output → ENNReal},
      ENNRealMeasurable (vectorBorel output) integrand →
      Problib.Measure.lintegral (law point) integrand =
        ENNReal.tsum (fun index => (pieces index).traceIntegral point integrand)) :
    Certificate law where
  pieces := pieces
  law_eq := fun point => by
    rw [Measure.eq_iff_lintegral]
    intro integrand measurable
    rw [integral point measurable, lintegral_sum_measure]
    exact ENNReal.tsum_congr (fun index =>
      ((pieces index).lintegral_kernel point measurable).symm)

/-- One piece certifies a kernel whose integrals are its trace integrals. -/
public noncomputable def ofPiece (piece : Piece environment output)
    (integral : ∀ point {integrand : carrier output → ENNReal},
      ENNRealMeasurable (vectorBorel output) integrand →
      Problib.Measure.lintegral (law point) integrand = piece.traceIntegral point integrand) :
    Certificate law :=
  ofLintegral (Piece.single piece) (fun point integrand measurable => by
    rw [Piece.tsum_single]
    exact integral point measurable)

/-- Equal kernels share certificates. -/
public def congr {other : Kernel (vectorBorel environment) (vectorBorel output)}
    (certificate : Certificate law) (equal : law = other) : Certificate other :=
  equal ▸ certificate

/-! ## Rules -/

/-- The zero kernel has the certificate of empty pieces. -/
public noncomputable def zero :
    Certificate (Kernel.zero (vectorBorel environment) (vectorBorel output)) :=
  ofLintegral (fun _ => Piece.empty environment output) (fun point integrand _ => by
    rw [Kernel.zero_apply, lintegral_zero_measure]
    rw [ENNReal.tsum_congr (fun _ => Piece.empty_traceIntegral point integrand)]
    exact ENNReal.tsum_zero.symm)

/-- A partial deterministic return: the Dirac mass at the value on the value's
domain, and zero off it. One weightless piece certifies it. -/
public noncomputable def retPartial (value : PartialPAP environment output) :
    Certificate (Kernel.piecewise value.domain (c_analytic_measurable value.c_analytic_domain)
      (Kernel.deterministic value.totalize value.totalize_measurable)
      (Kernel.zero (vectorBorel environment) (vectorBorel output))) :=
  let lifted := (PartialPAP.ofAnalytic leftVector (leftVector_analytic environment 0)).comp value
  ofPiece (Piece.atom lifted (fun _ => ENNReal.one) (ENNRealMeasurable.constant _ _))
    (fun point integrand measurable => by
      rw [Piece.atom_traceIntegral _ _ _ _ measurable]
      have domain : lifted.domain (pairVector point Piece.emptyTrace) ↔ value.domain point := by
        rw [PartialPAP.comp_domain, PartialPAP.ofAnalytic_totalize, leftVector_pairVector]
        exact ⟨fun both => both.2,
          fun member => ⟨PartialPAP.ofAnalytic_domain _ _ _, member⟩⟩
      by_cases member : value.domain point
      · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member, Kernel.deterministic_apply,
          lintegral_dirac _ _ measurable, ennrealIndicator_of_mem (domain.mpr member),
          PartialPAP.comp_totalize _ _ (domain.mpr member), PartialPAP.ofAnalytic_totalize,
          leftVector_pairVector, ENNReal.one_mul]
      · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member, Kernel.zero_apply,
          lintegral_zero_measure,
          ennrealIndicator_of_not_mem (fun other => member (domain.mp other)),
          ENNReal.zero_mul])

/-- A total deterministic return. -/
public noncomputable def ret (value : PartialPAP environment output)
    (total : ∀ point, value.domain point) :
    Certificate (Kernel.deterministic value.totalize value.totalize_measurable) :=
  (retPartial value).congr (Kernel.ext fun point =>
    Kernel.piecewise_apply_of_mem _ _ _ _ _ (total point))

/-- A score: the weight at the environment times the Dirac mass at the unit
point, as the kernel semantics scores. The weight need only be measurable. -/
public noncomputable def score (weight : carrier environment → ENNReal)
    (measurable : ENNRealMeasurable (vectorBorel environment) weight) :
    Certificate ((Kernel.deterministic (fun _ => zeroVector 0)
        (MeasurableMap.constant (vectorBorel environment) (vectorBorel 0) (zeroVector 0))).withDensity
      (Kernel.IsSFinite.deterministic _ _) (fun point _ => weight point)
      (measurable.comp (Space.first_measurable _ _))) :=
  ofPiece (Piece.atom
      (PartialPAP.ofAnalytic (fun _ => zeroVector 0) (Piece.constant_analytic _ _))
      (fun point => weight (leftVector point)) (measurable.comp (leftVector_measurable _ _)))
    (fun point integrand integrandMeasurable => by
      rw [Kernel.lintegral_withDensity _ _ _ point integrandMeasurable,
        Kernel.deterministic_apply,
        lintegral_dirac _ _ (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _)
          integrandMeasurable),
        Piece.atom_traceIntegral _ _ _ _ integrandMeasurable,
        ennrealIndicator_of_mem (PartialPAP.ofAnalytic_domain _ _ _),
        PartialPAP.ofAnalytic_totalize, leftVector_pairVector])

/-- A draw from Lebesgue measure on `dimension` coordinates, weighted by a
density jointly measurable in the environment and the draw. A uniform draw is
the indicator of the unit cube. -/
public noncomputable def draw {dimension : Nat}
    (density : carrier (environment + dimension) → ENNReal)
    (measurable : ENNRealMeasurable (vectorBorel (environment + dimension)) density) :
    Certificate ((Kernel.const (target := vectorBorel dimension) (vectorBorel environment)
        (volumePi dimension)).withDensity
      (Kernel.IsSFinite.const _ (volumePiSFinite dimension))
      (fun point trace => density (pairVector point trace))
      (measurable.comp (pairVector_measurable _ _))) :=
  ofPiece ⟨dimension, PartialPAP.ofAnalytic rightVector (rightVector_analytic _ _),
      density, measurable⟩
    (fun point integrand integrandMeasurable => by
      refine (Kernel.lintegral_withDensity _ _ _ point integrandMeasurable).trans ?_
      apply lintegral_congr
      intro trace
      change _ = ENNReal.mul (ennrealIndicator _ density _) (integrand
        ((PartialPAP.ofAnalytic rightVector (rightVector_analytic _ _)).totalize _))
      rw [ennrealIndicator_of_mem (PartialPAP.ofAnalytic_domain _ _ _),
        PartialPAP.ofAnalytic_totalize, rightVector_pairVector])

/-- A countable sum of certified kernels, as `superpose` and the strata of a
recursion: the pieces are Cantor-flattened. -/
public noncomputable def sum {family : Nat → Kernel (vectorBorel environment) (vectorBorel output)}
    (certificates : ∀ index, Certificate (family index)) : Certificate (Kernel.sum family) :=
  ofLintegral
    (fun index =>
      let pair := Problib.Countable.Pair.decode index
      (certificates pair.1).pieces pair.2)
    (fun point integrand measurable => by
      rw [Kernel.sum_apply, lintegral_sum_measure,
        ENNReal.tsum_congr (fun index => (certificates index).lintegral point measurable)]
      exact (ENNReal.tsum_flatten (fun row column =>
        ((certificates row).pieces column).traceIntegral point integrand)).symm)

/-- Substitution into the environment by a total joint PAP map. A call's
argument and a state update enter the invariant this way. -/
public noncomputable def precomp {source : Nat}
    {kernel : Kernel (vectorBorel source) (vectorBorel output)}
    (certificate : Certificate kernel) (substitution : PartialPAP environment source)
    (total : ∀ point, substitution.domain point) :
    Certificate (kernel.precomp substitution.totalize substitution.totalize_measurable) :=
  ofLintegral (fun index => (certificate.pieces index).substitute substitution)
    (fun point integrand measurable => by
      rw [Kernel.precomp_apply, certificate.lintegral _ measurable]
      exact ENNReal.tsum_congr (fun index =>
        ((certificate.pieces index).substitute_traceIntegral total point integrand).symm))

/-- The rows of a case split: the first branch's pieces cut to the region, the
second's cut to its complement. -/
@[expose] public noncomputable def caseRows {region : Set (carrier environment)}
    (regionAnalytic : CAnalytic region) (complementAnalytic : CAnalytic (Set.complement region))
    (pieces others : Nat → Piece environment output) : Nat → Nat → Piece environment output
  | 0, column => (pieces column).restrict regionAnalytic
  | 1, column => (others column).restrict complementAnalytic
  | _ + 2, _ => Piece.empty environment output

/-- A case split on a c-analytic region whose complement is c-analytic, as a
guard's sign or a sum value's tag selects a branch. -/
public noncomputable def cases {region : Set (carrier environment)}
    (regionAnalytic : CAnalytic region) (complementAnalytic : CAnalytic (Set.complement region))
    {left right : Kernel (vectorBorel environment) (vectorBorel output)}
    (inside : Certificate left) (outside : Certificate right) :
    Certificate (Kernel.piecewise region (c_analytic_measurable regionAnalytic) left right) :=
  let rows := caseRows regionAnalytic complementAnalytic inside.pieces outside.pieces
  ofLintegral
    (fun index =>
      let pair := Problib.Countable.Pair.decode index
      rows pair.1 pair.2)
    (fun point integrand measurable => by
      refine Eq.trans ?_ (ENNReal.tsum_flatten (fun row column =>
        (rows row column).traceIntegral point integrand)).symm
      have each : ∀ row, ENNReal.tsum (fun column => (rows row column).traceIntegral point integrand) =
          ENNReal.pair
            (ENNReal.tsum (fun column =>
              ((inside.pieces column).restrict regionAnalytic).traceIntegral point integrand))
            (ENNReal.tsum (fun column =>
              ((outside.pieces column).restrict complementAnalytic).traceIntegral point integrand))
            row := by
        intro row
        match row with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 =>
          exact (ENNReal.tsum_congr (fun _ => Piece.empty_traceIntegral point integrand)).trans
            ENNReal.tsum_zero
      rw [ENNReal.tsum_congr each, ENNReal.tsum_pair]
      by_cases member : region point
      · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member, inside.lintegral point measurable,
          ENNReal.tsum_congr (fun column =>
            (inside.pieces column).restrict_traceIntegral_of_mem regionAnalytic member integrand),
          ENNReal.tsum_congr (fun column =>
            (outside.pieces column).restrict_traceIntegral_of_not_mem complementAnalytic
              (fun other => other member) integrand),
          ENNReal.tsum_zero, ENNReal.add_zero]
      · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member, outside.lintegral point measurable,
          ENNReal.tsum_congr (fun column =>
            (inside.pieces column).restrict_traceIntegral_of_not_mem regionAnalytic member integrand),
          ENNReal.tsum_congr (fun column =>
            (outside.pieces column).restrict_traceIntegral_of_mem complementAnalytic member
              integrand),
          ENNReal.tsum_zero, ENNReal.zero_add])

/-- Normalization at every input, as the kernel semantics normalizes: each
weight is divided by the mass at its environment. The mass need only be
measurable, so the new weights stay jointly measurable whether or not it is
PAP. -/
public noncomputable def normalize (certificate : Certificate law) (finite : Kernel.IsSFinite law) :
    Certificate (law.withDensity finite
      (fun point _ => ENNReal.densityRatio ENNReal.one (law point Set.univ))
      ((ENNRealMeasurable.densityRatio (ENNRealMeasurable.constant _ ENNReal.one)
        (law.measurable (vectorBorel output).univ)).comp (Space.first_measurable _ _))) :=
  let mass := ENNRealMeasurable.densityRatio (ENNRealMeasurable.constant _ ENNReal.one)
    (law.measurable (vectorBorel output).univ)
  ofLintegral (fun index => (certificate.pieces index).scale _ mass)
    (fun point integrand measurable => by
      refine (Kernel.lintegral_withDensity _ _ _ point measurable).trans ?_
      rw [lintegral_smul _ _ measurable, certificate.lintegral point measurable,
        ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_congr (fun index =>
        ((certificate.pieces index).scale_traceIntegral mass point measurable).symm))

/-- Certificates for strata, each built from those at every smaller count. -/
public noncomputable def stratumCertificates
    (strata : Nat → Kernel (vectorBorel environment) (vectorBorel output))
    (zero : strata 0 = Kernel.zero (vectorBorel environment) (vectorBorel output))
    (step : (count : Nat) → ((earlier : Fin (count + 1)) → Certificate (strata earlier)) →
      Certificate (strata (count + 1))) :
    (count : Nat) → Certificate (strata count) :=
  fun count => Nat.strongRecOn count (fun current previous =>
    match current, previous with
    | 0, _ => Certificate.zero.congr zero.symm
    | count + 1, previous => step count (fun earlier => previous earlier earlier.isLt))

/-- A kernel that is the sum of its strata is certified when the zero stratum
vanishes and each stratum is certified from those at every smaller count, as a
recursion's stratum at count `n + 1` reads its strata at the counts its calls
split `n` into. -/
public noncomputable def ofStrata
    (strata : Nat → Kernel (vectorBorel environment) (vectorBorel output))
    (decomposition : ∀ point, law point = Measure.sum (fun count => strata count point))
    (zero : strata 0 = Kernel.zero (vectorBorel environment) (vectorBorel output))
    (step : (count : Nat) → ((earlier : Fin (count + 1)) → Certificate (strata earlier)) →
      Certificate (strata (count + 1))) :
    Certificate law :=
  (Certificate.sum (stratumCertificates strata zero step)).congr
    (Kernel.ext fun point => (decomposition point).symm)

/-- The kernel semantics' bind on Euclidean components: the continuation reads
the first value ahead of the environment. -/
@[expose] public noncomputable def bindKernel {middle : Nat} {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (vectorBorel middle)) (finite : Kernel.IsSFinite first)
    (continuation : Kernel (vectorBorel (middle + environment)) target) :
    Kernel (vectorBorel environment) target :=
  ((first.attach finite).map (fun pair => pairVector pair.2 pair.1)
    (MeasurableMap.comp (pairVector_measurable _ _) (Space.swap_measurable _ _))).comp continuation

public theorem bindKernel_lintegral {middle : Nat} {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (vectorBorel middle)) (finite : Kernel.IsSFinite first)
    (continuation : Kernel (vectorBorel (middle + environment)) target)
    (point : carrier environment) {integrand : τ → ENNReal}
    (measurable : ENNRealMeasurable target integrand) :
    Problib.Measure.lintegral (bindKernel first finite continuation point) integrand =
      Problib.Measure.lintegral (first point)
        (fun value => Problib.Measure.lintegral (continuation (pairVector value point)) integrand) := by
  have continued := Kernel.lintegral_measurable continuation measurable
  refine (Kernel.lintegral_comp _ _ point measurable).trans ?_
  refine (lintegral_map _ _ (MeasurableMap.comp (pairVector_measurable _ _)
    (Space.swap_measurable _ _)) continued).trans ?_
  exact lintegral_map _ _ (Kernel.pair_left_measurable point) (continued.comp
    (MeasurableMap.comp (pairVector_measurable _ _) (Space.swap_measurable _ _)))

/-- Bind: the pieces pair a first piece with a continuation piece, the
continuation's return map composed after the first value's substitution.
Neither weight need be more than measurable. -/
public noncomputable def bind {middle : Nat}
    {first : Kernel (vectorBorel environment) (vectorBorel middle)}
    {continuation : Kernel (vectorBorel (middle + environment)) (vectorBorel output)}
    (source : Certificate first) (finite : Kernel.IsSFinite first)
    (rest : Certificate continuation) :
    Certificate (bindKernel first finite continuation) :=
  ofLintegral
    (fun index =>
      let pair := Problib.Countable.Pair.decode index
      (source.pieces pair.1).bind (rest.pieces pair.2))
    (fun point integrand measurable => by
      rw [bindKernel_lintegral _ _ _ point measurable,
        source.lintegral point ((Kernel.lintegral_measurable continuation measurable).comp
          (MeasurableMap.comp (pairVector_measurable _ _)
            (Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ point))))]
      refine Eq.trans ?_ (ENNReal.tsum_flatten (fun row column =>
        ((source.pieces row).bind (rest.pieces column)).traceIntegral point integrand)).symm
      exact ENNReal.tsum_congr (fun row =>
        (source.pieces row).traceIntegral_bind_tsum rest.pieces point measurable
          (fun value => rest.lintegral value measurable)))

/-- The regular-weight contract a faithful consumer needs beyond the bare
invariant: on each piece's domain the weight is finite and its real value is
PAP. Off the domain the law ignores the weight. `normalize` does not preserve
this in general, since a measurable reciprocal need not be PAP, so the bare
certificate carries no such claim. -/
public structure Regular (certificate : Certificate law) : Prop where
  finite : ∀ index point, (certificate.pieces index).map.domain point →
    ENNReal.Finite ((certificate.pieces index).weight point)
  representation : ∀ index, ∃ value : PartialPAP (environment + (certificate.pieces index).dimension) 1,
    value.domain = (certificate.pieces index).map.domain ∧
      ∀ point, value.domain point →
        value.totalize point 0 = ENNReal.toReal ((certificate.pieces index).weight point)

end Certificate

/-! ## Keyed outputs

A sum-valued output is a countable family of Euclidean components on the
dependent sum of their carriers. A component's kernel restricts the law to that
component's fiber and reads the payload back through the injection, so a keyed
certificate is one certificate per component, and the component index is the
key of each of its pieces. Countability enters through an injective code.
-/

section Keyed

variable {Key : Type} [DecidableEq Key] {outputs : Key → Nat} {environment : Nat}

/-- The dependent sum of the output components. -/
@[expose] public def keyedSpace (outputs : Key → Nat) : Space (Σ key, carrier (outputs key)) :=
  Space.sigma (fun key => vectorBorel (outputs key))

omit [DecidableEq Key] in
public theorem sigma_mk_image_measurable (key : Key) (region : Set (carrier (outputs key)))
    (measurable : (vectorBorel (outputs key)).Measurable region) :
    (keyedSpace outputs).Measurable
      (Set.image (Sigma.mk (β := fun key => carrier (outputs key)) key) region) := by
    intro index
    by_cases same : index = key
    · subst same
      have equal : (fun value => Set.image (Sigma.mk (β := fun key => carrier (outputs key)) index)
          region ⟨index, value⟩) = region := by
        funext value
        exact propext ⟨fun ⟨_, member, equal⟩ => eq_of_heq (Sigma.mk.inj equal).2 ▸ member,
          fun member => ⟨value, member, rfl⟩⟩
      change (vectorBorel (outputs index)).Measurable
        (fun value => Set.image (Sigma.mk (β := fun key => carrier (outputs key)) index)
          region ⟨index, value⟩)
      rw [equal]
      exact measurable
    · have equal : (fun value => Set.image (Sigma.mk (β := fun key => carrier (outputs key)) key)
          region ⟨index, value⟩) = Set.empty := by
        funext value
        exact propext ⟨fun ⟨_, _, equal⟩ => same (Sigma.mk.inj equal).1.symm, False.elim⟩
      change (vectorBorel (outputs index)).Measurable
        (fun value => Set.image (Sigma.mk (β := fun key => carrier (outputs key)) key)
          region ⟨index, value⟩)
      rw [equal]
      exact (vectorBorel (outputs index)).empty

/-- One component's injection into the dependent sum. -/
@[expose] public def injection (outputs : Key → Nat) (key : Key) :
    MeasurableEmbedding (vectorBorel (outputs key)) (keyedSpace outputs) where
  function := Sigma.mk (β := fun key => carrier (outputs key)) key
  injective := fun _ _ equal => eq_of_heq (Sigma.mk.inj equal).2
  measurable := MeasurableMap.sigma_mk (fun key => vectorBorel (outputs key)) key
  image_measurable := sigma_mk_image_measurable (outputs := outputs) key

omit [DecidableEq Key] in
@[simp] public theorem injection_function (key : Key) :
    (injection outputs key).function = Sigma.mk (β := fun key => carrier (outputs key)) key := rfl

/-- One component of a keyed kernel: the law restricted to the component's
fiber, read back through its injection. Reading the payload without the
restriction would add the other components' mass at a default point. -/
@[expose] public noncomputable def componentKernel {α : Type} {source : Space α} (key : Key)
    (law : Kernel source (keyedSpace outputs)) : Kernel source (vectorBorel (outputs key)) :=
  law.comap (injection outputs key)

/-- C8's joint invariant on a keyed output: a certificate for every component. -/
@[expose] public def KeyedCertificate (law : Kernel (vectorBorel environment) (keyedSpace outputs)) :
    Type :=
  (key : Key) → Certificate (componentKernel key law)

/-- The key coded `index`, when one exists. -/
@[expose] public noncomputable def keyAt (code : Key → Nat) (index : Nat) : Option Key :=
  open Classical in
  if found : ∃ key, code key = index then some (Classical.choose found) else none

omit [DecidableEq Key] in
public theorem keyAt_code {code : Key → Nat} (injective : Function.Injective code) (key : Key) :
    keyAt code (code key) = some key := by
  have found : ∃ other, code other = code key := ⟨key, rfl⟩
  unfold keyAt
  rw [dite_eq_left found]
  exact congrArg some (injective (Classical.choose_spec found))

/-- The points whose key is coded `index`. -/
@[expose] public def codedFiber (code : Key → Nat) (index : Nat) : Set (Σ key, carrier (outputs key)) :=
  fun point => code point.1 = index

omit [DecidableEq Key] in
theorem codedFiber_some {code : Key → Nat} (injective : Function.Injective code) {index : Nat}
    {key : Key} (found : keyAt code index = some key) :
    codedFiber (outputs := outputs) code index =
      Set.range (Sigma.mk (β := fun key => carrier (outputs key)) key) := by
  unfold keyAt at found
  split at found
  · rename_i exists_key
    cases found
    funext point
    apply propext
    constructor
    · intro coded
      obtain ⟨first, value⟩ := point
      have same : first = Classical.choose exists_key :=
        injective (coded.trans (Classical.choose_spec exists_key).symm)
      subst same
      exact ⟨value, rfl⟩
    · rintro ⟨value, rfl⟩
      exact Classical.choose_spec exists_key
  · cases found

omit [DecidableEq Key] in
theorem codedFiber_none {code : Key → Nat} {index : Nat} (missing : keyAt code index = none) :
    codedFiber (outputs := outputs) code index = Set.empty := by
  unfold keyAt at missing
  split at missing
  · cases missing
  · rename_i none_key
    funext point
    exact propext ⟨fun coded => none_key ⟨point.1, coded⟩, False.elim⟩

omit [DecidableEq Key] in
/-- The assembly law: a keyed measure is the sum over keys of its components,
each pushed back into the dependent sum. -/
public theorem assembly {code : Key → Nat} (injective : Function.Injective code)
    (measure : Measure (keyedSpace outputs)) :
    measure = Measure.sum (fun index => match keyAt code index with
      | some key => (measure.comap (injection outputs key)).map
          (injection outputs key).function (injection outputs key).measurable
      | none => Measure.zero (keyedSpace outputs)) := by
  have pieces : ∀ index, (match keyAt code index with
      | some key => (measure.comap (injection outputs key)).map
          (injection outputs key).function (injection outputs key).measurable
      | none => Measure.zero (keyedSpace outputs)) = measure.restrict (codedFiber code index) := by
    intro index
    cases found : keyAt code index with
    | some key =>
        refine (Measure.map_comap measure (injection outputs key)).trans ?_
        rw [injection_function, codedFiber_some injective found]
    | none => exact ((congrArg measure.restrict (codedFiber_none found)).trans
        (Measure.restrict_empty measure)).symm
  rw [funext pieces]
  apply Measure.ext
  intro set measurable
  have fiberMeasurable : ∀ index, (keyedSpace outputs).Measurable (codedFiber code index) :=
    fun index => MeasurableMap.sigma_fst _ (Space.discrete_measurable (fun key => code key = index))
  rw [Measure.sum_apply _ measurable, ENNReal.tsum_congr (fun index =>
      Measure.restrict_apply measure _ measurable),
    ← measure.iUnion_disjoint _ (fun index => (keyedSpace outputs).inter measurable (fiberMeasurable index))
      (fun left right different _ inLeft inRight => different (inLeft.2.symm.trans inRight.2))]
  congr 1
  funext point
  exact propext ⟨fun member => ⟨code point.1, member, rfl⟩, fun ⟨_, member, _⟩ => member⟩

omit [DecidableEq Key] in
/-- Integrating against a keyed measure sums each component's integral over its
own carrier. -/
public theorem lintegral_components {code : Key → Nat} (injective : Function.Injective code)
    (measure : Measure (keyedSpace outputs)) {integrand : (Σ key, carrier (outputs key)) → ENNReal}
    (measurable : ENNRealMeasurable (keyedSpace outputs) integrand) :
    lintegral measure integrand = ENNReal.tsum (fun index => match keyAt code index with
      | some key => lintegral (measure.comap (injection outputs key))
          (fun value => integrand ⟨key, value⟩)
      | none => ENNReal.zero) := by
  refine (congrArg (fun whole => lintegral whole integrand) (assembly injective measure)).trans ?_
  refine (lintegral_sum_measure _ _).trans (ENNReal.tsum_congr fun index => ?_)
  cases keyAt code index with
  | some key =>
      exact lintegral_map (measure.comap (injection outputs key))
        (injection outputs key).function (injection outputs key).measurable measurable
  | none => exact lintegral_zero_measure _

/-- Every component's continuation, reading that component's value ahead of
the environment. -/
@[expose] public noncomputable def keyedContinuation {τ : Type} {target : Space τ}
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target) :
    Kernel (Space.sigma fun key => vectorBorel (outputs key + environment)) target where
  toFun point := continuation point.1 point.2
  measurable := fun measurable threshold key => (continuation key).measurable measurable threshold

public theorem keyedPair_measurable {code : Key → Nat} (injective : Function.Injective code) :
    MeasurableMap (Space.product (vectorBorel environment) (keyedSpace outputs))
      (Space.sigma fun key => vectorBorel (outputs key + environment))
      (fun pair => (⟨pair.2.1, pairVector pair.2.2 pair.1⟩ :
        Σ key, carrier (outputs key + environment))) :=
  MeasurableMap.comp
    (MeasurableMap.from_sigma_iff (β := fun key => carrier (outputs key) × carrier environment)
      (function := fun input => (⟨input.1, pairVector input.2.1 input.2.2⟩ :
        Σ key, carrier (outputs key + environment))).mpr fun key =>
      MeasurableMap.comp (MeasurableMap.sigma_mk _ key) (pairVector_measurable _ _))
    (MeasurableMap.comp (MeasurableMap.sigma_distribute
      (spaces := fun key => vectorBorel (outputs key)) code injective) (Space.swap_measurable _ _))

/-- Bind from a keyed first value: the continuation of the value's component
reads its payload ahead of the environment. -/
@[expose] public noncomputable def keyedBindKernel {code : Key → Nat}
    (injective : Function.Injective code) {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (keyedSpace outputs)) (finite : Kernel.IsSFinite first)
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target) :
    Kernel (vectorBorel environment) target :=
  ((first.attach finite).map _ (keyedPair_measurable injective)).comp (keyedContinuation continuation)

omit [DecidableEq Key] in
private theorem keyedIntegrand_measurable {τ : Type} {target : Space τ}
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target)
    (point : carrier environment) {integrand : τ → ENNReal}
    (measurable : ENNRealMeasurable target integrand) :
    ENNRealMeasurable (keyedSpace outputs) (fun value =>
      lintegral (continuation value.1 (pairVector value.2 point)) integrand) :=
  fun threshold key => (Kernel.lintegral_measurable (continuation key) measurable).comp
    (MeasurableMap.comp (pairVector_measurable _ _)
      (Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ point))) threshold

public theorem keyedBindKernel_lintegral {code : Key → Nat} (injective : Function.Injective code)
    {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (keyedSpace outputs)) (finite : Kernel.IsSFinite first)
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target)
    (point : carrier environment) {integrand : τ → ENNReal}
    (measurable : ENNRealMeasurable target integrand) :
    lintegral (keyedBindKernel injective first finite continuation point) integrand =
      lintegral (first point) (fun value =>
        lintegral (continuation value.1 (pairVector value.2 point)) integrand) := by
  have continued := Kernel.lintegral_measurable (keyedContinuation continuation) measurable
  refine (Kernel.lintegral_comp _ _ point measurable).trans ?_
  refine (lintegral_map _ _ (keyedPair_measurable injective) continued).trans ?_
  exact lintegral_map _ _ (Kernel.pair_left_measurable point)
    (continued.comp (keyedPair_measurable injective))

/-- The binds of each component into its continuation, indexed by code. -/
@[expose] public noncomputable def componentBinds (code : Key → Nat) {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (keyedSpace outputs))
    (finite : (key : Key) → Kernel.IsSFinite (componentKernel key first))
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target)
    (index : Nat) : Kernel (vectorBorel environment) target :=
  match keyAt code index with
  | some key => Certificate.bindKernel (componentKernel key first) (finite key) (continuation key)
  | none => Kernel.zero _ _

/-- A keyed bind is the sum over keys of each component's bind. -/
public theorem keyedBindKernel_eq_sum {code : Key → Nat} (injective : Function.Injective code)
    {τ : Type} {target : Space τ}
    (first : Kernel (vectorBorel environment) (keyedSpace outputs)) (finite : Kernel.IsSFinite first)
    (componentFinite : (key : Key) → Kernel.IsSFinite (componentKernel key first))
    (continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) target) :
    keyedBindKernel injective first finite continuation =
      Kernel.sum (componentBinds code first componentFinite continuation) := by
  apply Kernel.ext
  intro point
  rw [Measure.eq_iff_lintegral]
  intro integrand measurable
  rw [keyedBindKernel_lintegral _ _ _ _ point measurable, Kernel.sum_apply, lintegral_sum_measure,
    lintegral_components injective _ (keyedIntegrand_measurable continuation point measurable)]
  apply ENNReal.tsum_congr
  intro index
  unfold componentBinds
  cases keyAt code index with
  | some key =>
      exact (Certificate.bindKernel_lintegral (componentKernel key first)
        (componentFinite key) (continuation key) point measurable).symm
  | none => exact (lintegral_zero_measure _).symm

omit [DecidableEq Key] in
/-- A component of a bind is the bind into that component. -/
public theorem componentKernel_bind {middle : Nat}
    (first : Kernel (vectorBorel environment) (vectorBorel middle)) (finite : Kernel.IsSFinite first)
    (continuation : Kernel (vectorBorel (middle + environment)) (keyedSpace outputs)) (key : Key) :
    componentKernel key (Certificate.bindKernel first finite continuation) =
      Certificate.bindKernel first finite (componentKernel key continuation) := by
  apply Kernel.ext_measurable
  intro point set measurable
  unfold componentKernel Certificate.bindKernel
  rw [Kernel.comap_apply, Measure.comap_apply _ _ measurable,
    Kernel.comp_apply_measurable _ _ _ ((injection outputs key).image_measurable set measurable),
    Kernel.comp_apply_measurable _ _ _ measurable]
  apply lintegral_congr
  intro value
  rw [Kernel.comap_apply, Measure.comap_apply _ _ measurable]

/-- The keyed bind: a certificate for every component of the first value and
for every component's continuation certifies the bind, piece by piece. -/
public noncomputable def Certificate.keyedBind {code : Key → Nat}
    (injective : Function.Injective code) {output : Nat}
    {first : Kernel (vectorBorel environment) (keyedSpace outputs)}
    {continuation : (key : Key) → Kernel (vectorBorel (outputs key + environment)) (vectorBorel output)}
    (source : KeyedCertificate first) (finite : Kernel.IsSFinite first)
    (rest : (key : Key) → Certificate (continuation key)) :
    Certificate (keyedBindKernel injective first finite continuation) :=
  (Certificate.sum (family := componentBinds code first (fun key => (source key).sfinite) continuation)
    (fun index => by
      unfold componentBinds
      cases keyAt code index with
      | some key => exact Certificate.bind (source key) _ (rest key)
      | none => exact Certificate.zero)).congr
    (keyedBindKernel_eq_sum injective first finite _ continuation).symm

/-- A keyed return: a deterministic sum-valued leaf whose key preimages are the
domains of partial PAP returns, one per key. The domains are then pairwise
disjoint and cover the environment. -/
public noncomputable def KeyedCertificate.ret (values : (key : Key) → PartialPAP environment (outputs key))
    {leaf : carrier environment → Σ key, carrier (outputs key)}
    (measurable : MeasurableMap (vectorBorel environment) (keyedSpace outputs) leaf)
    (keyed : ∀ key point, (values key).domain point ↔ (leaf point).1 = key)
    (payload : ∀ key point, (values key).domain point → leaf point = ⟨key, (values key).totalize point⟩) :
    KeyedCertificate (Kernel.deterministic leaf measurable) := fun key =>
  (Certificate.retPartial (values key)).congr (Kernel.ext_measurable fun point set setMeasurable => by
    refine Eq.trans ?_ (Measure.comap_apply _ _ setMeasurable).symm
    rw [injection_function, Kernel.deterministic_apply,
      Measure.dirac_apply _ _ (sigma_mk_image_measurable (outputs := outputs) key set setMeasurable)]
    by_cases member : (values key).domain point
    · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member, Kernel.deterministic_apply,
        Measure.dirac_apply _ _ setMeasurable, payload key point member]
      by_cases inside : set ((values key).totalize point)
      · rw [ite_eq_left inside, ite_eq_left ⟨_, inside, rfl⟩]
      · rw [ite_eq_right inside, ite_eq_right fun ⟨_, found, equal⟩ =>
          inside (eq_of_heq (Sigma.mk.inj equal).2 ▸ found)]
    · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member, Kernel.zero_apply,
        ite_eq_right fun ⟨_, _, equal⟩ => member ((keyed key point).mpr (congrArg Sigma.fst equal).symm),
        Measure.zero_apply])

end Keyed

end Problib.Analysis.PAP.Trace
