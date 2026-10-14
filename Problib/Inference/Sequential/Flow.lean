module

public import Problib.Inference.Sequential
public import Problib.Measure.Kernel.Density

set_option autoImplicit false

/-! Feynman–Kac flows.

A stage proposes `y` from a kernel `M(x, ·)` and then weighs the pair by a potential `G(x, y)`, so
its unnormalized transition is `Q(x, dy) = G(x, y) M(x, dy)` (`Stage.kernel`). A flow is a finite
sequence of stages whose spaces may all differ (`Flow`). From any initial measure `γ₀` it induces
`γ_{t+1} = γ_t.bind Q_t` (`Flow.induced`), which is `γ₀` bound through the composed kernel
(`Flow.induced_eq_bind`). Integrating a test against the induced measure integrates its backward
image `B_t f(x) = ∫ M_t(x, dy) G_t(x, y) B_{t+1} f(y)` against `γ₀` (`Flow.lintegral_induced`), and
the evidence is the induced mass (`Flow.evidence_eq`).

Nothing is normalized. Proposals need not be Markov, potentials may be infinite, and the initial
mass is arbitrary: a zero initial measure or a zero potential gives the zero measure whatever
follows (`Flow.induced_zero`, `Flow.induced_zero_stage`). S-finiteness of the initial measure is
asked only to conclude it of the induced one (`Flow.inducedFinite`). A stage with a finite
potential is the barycenter of the increment kernel (`Stage.ofIncrement_kernel`), so `SeqRN` is the
one-stage flow (`seq_rn_iff_stage`). A population whose expected empirical measure is the induced
measure estimates every nonnegative test and the evidence without bias (`Flow.population_test`,
`Flow.population_evidence`). -/

namespace Problib.Inference.FeynmanKac

open Problib.Real Problib.Measure

universe u v

public section

/-- One stage: a proposal kernel and a potential on the full input/output pair. -/
structure Stage {α : Type u} {β : Type v} (source : Space α) (target : Space β) where
  proposal : Kernel source target
  proposalFinite : Kernel.IsSFinite proposal
  potential : α × β → ENNReal
  potentialMeasurable : ENNRealMeasurable (Space.product source target) potential

namespace Stage

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- The unnormalized transition `Q(x, dy) = G(x, y) M(x, dy)`. -/
@[expose] noncomputable def kernel (stage : Stage source target) : Kernel source target :=
  stage.proposal.withDensity stage.proposalFinite
    (fun input output => stage.potential (input, output)) stage.potentialMeasurable

/-- The transition is s-finite, whatever the potential. -/
@[expose] noncomputable def kernelFinite (stage : Stage source target) :
    Kernel.IsSFinite stage.kernel :=
  Kernel.IsSFinite.withDensity stage.proposalFinite
    (fun input output => stage.potential (input, output)) stage.potentialMeasurable

theorem lintegral_kernel (stage : Stage source target) (input : α) {function : β → ENNReal}
    (measurable : ENNRealMeasurable target function) :
    lintegral (stage.kernel input) function = lintegral (stage.proposal input) (fun output =>
      ENNReal.mul (stage.potential (input, output)) (function output)) :=
  Kernel.lintegral_withDensity stage.proposal stage.proposalFinite
    (density := fun input output => stage.potential (input, output))
    stage.potentialMeasurable input measurable

/-- The stage of a finite increment. -/
@[expose] noncomputable def ofIncrement (proposal : Kernel source target)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product source target) weightSpace increment) :
    Stage source target where
  proposal := proposal
  proposalFinite := proposalFinite
  potential := fun pair => ENNReal.finite (increment pair)
  potentialMeasurable := finite_weight_measurable incrementMeasurable

/-- A finite-increment stage moves mass as the barycenters of the increment kernel do. -/
theorem ofIncrement_kernel (proposal : Kernel source target)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product source target) weightSpace increment) :
    (ofIncrement proposal proposalFinite increment incrementMeasurable).kernel =
      barycenterKernel (incrementKernel proposal proposalFinite increment incrementMeasurable) := by
  apply Kernel.ext
  intro input
  exact (barycenterKernel_increment proposal proposalFinite increment incrementMeasurable
    input).symm

end Stage

/-- `SeqRN` is the one-stage flow of its proposal and increment. -/
theorem seq_rn_iff_stage {α : Type u} {β : Type v} {space : Space α} {result : Space β}
    {source : Measure space} {target : Measure result} {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    SeqRN source target proposal increment ↔ source.bind
      (Stage.ofIncrement proposal proposalFinite increment incrementMeasurable).kernel = target := by
  rw [Stage.ofIncrement_kernel]
  exact seq_rn_iff_bind proposalFinite incrementMeasurable

/-- A finite sequence of stages from a first space to a last. -/
inductive Flow : {first last : Type u} → Space first → Space last → Type (u + 1)
  | empty {current : Type u} (space : Space current) : Flow space space
  | stage {current middle last : Type u} {space : Space current} {middleSpace : Space middle}
      {lastSpace : Space last} (head : Stage space middleSpace)
      (rest : Flow middleSpace lastSpace) : Flow space lastSpace

namespace Flow

/-- The stages composed in execution order. -/
@[expose] noncomputable def kernel : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → Flow firstSpace lastSpace → Kernel firstSpace lastSpace
  | _, _, _, _, empty space =>
      Kernel.deterministic (fun state => state) (MeasurableMap.identity space)
  | _, _, _, _, stage head rest => head.kernel.comp rest.kernel

/-- The composed kernel is s-finite. -/
@[expose] noncomputable def kernelFinite : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → (flow : Flow firstSpace lastSpace) → Kernel.IsSFinite flow.kernel
  | _, _, _, _, empty space =>
      Kernel.IsSFinite.deterministic (fun state => state) (MeasurableMap.identity space)
  | _, _, _, _, stage head rest => Kernel.IsSFinite.comp head.kernelFinite rest.kernelFinite

/-- The measure a flow induces from an initial one: bind each stage in turn. -/
@[expose] noncomputable def induced : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → Flow firstSpace lastSpace → Measure firstSpace → Measure lastSpace
  | _, _, _, _, empty _, initial => initial
  | _, _, _, _, stage head rest, initial => rest.induced (initial.bind head.kernel)

/-- The backward action on tests: `B f(x) = ∫ M(x, dy) G(x, y) B' f(y)`, ending in `f`. -/
@[expose] noncomputable def backward : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → Flow firstSpace lastSpace → (last → ENNReal) → first → ENNReal
  | _, _, _, _, empty _, function => function
  | _, _, _, _, stage head rest, function => fun input =>
      lintegral (head.proposal input) (fun output =>
        ENNReal.mul (head.potential (input, output)) (rest.backward function output))

/-- The induced measure is the initial one bound through the composed kernel. -/
theorem induced_eq_bind : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → (flow : Flow firstSpace lastSpace) →
    (initial : Measure firstSpace) → flow.induced initial = initial.bind flow.kernel
  | _, _, _, _, empty space, initial => by
      rw [induced, kernel, Measure.bind_deterministic, Measure.map_id]
  | _, _, _, _, stage head rest, initial => by
      rw [induced, kernel, induced_eq_bind rest, Measure.bind_assoc]

theorem backward_measurable : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → (flow : Flow firstSpace lastSpace) →
    {function : last → ENNReal} → ENNRealMeasurable lastSpace function →
      ENNRealMeasurable firstSpace (flow.backward function)
  | _, _, _, _, empty _, _, measurable => measurable
  | _, _, _, _, stage head rest, function, measurable => by
      have equal : (stage head rest).backward function =
          fun input => lintegral (head.kernel input) (rest.backward function) :=
        funext fun input =>
          (head.lintegral_kernel input (backward_measurable rest measurable)).symm
      rw [equal]
      exact Kernel.lintegral_measurable head.kernel (backward_measurable rest measurable)

/-- Integrating against the induced measure integrates the backward image against the initial
one. -/
theorem lintegral_induced : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → (flow : Flow firstSpace lastSpace) →
    (initial : Measure firstSpace) → {function : last → ENNReal} →
    ENNRealMeasurable lastSpace function →
      lintegral (flow.induced initial) function = lintegral initial (flow.backward function)
  | _, _, _, _, empty _, _, _, _ => rfl
  | _, _, _, _, stage head rest, initial, function, measurable => by
      rw [induced, lintegral_induced rest _ measurable,
        Measure.lintegral_bind _ _ (backward_measurable rest measurable)]
      apply lintegral_congr
      intro input
      exact head.lintegral_kernel input (backward_measurable rest measurable)

variable {first last : Type u} {firstSpace : Space first} {lastSpace : Space last}

/-- The evidence: the mass the flow induces. -/
@[expose] noncomputable def evidence (flow : Flow firstSpace lastSpace)
    (initial : Measure firstSpace) : ENNReal :=
  flow.induced initial Set.univ

/-- The evidence is the initial integral of the backward image of one. -/
theorem evidence_eq (flow : Flow firstSpace lastSpace) (initial : Measure firstSpace) :
    flow.evidence initial = lintegral initial (flow.backward fun _ => ENNReal.one) := by
  have total := lintegral_const (flow.induced initial) ENNReal.one
  rw [ENNReal.one_mul] at total
  rw [evidence, ← total,
    lintegral_induced flow initial (ENNRealMeasurable.constant lastSpace ENNReal.one)]

/-- From an s-finite initial measure the induced measure is s-finite. -/
noncomputable def inducedFinite (flow : Flow firstSpace lastSpace) {initial : Measure firstSpace}
    (initialFinite : Measure.SFinite initial) : Measure.SFinite (flow.induced initial) := by
  rw [induced_eq_bind]
  exact initialFinite.bind flow.kernelFinite

/-- The empty flow leaves the initial measure as it is. -/
theorem induced_empty (initial : Measure firstSpace) :
    (empty firstSpace).induced initial = initial :=
  rfl

/-- No initial mass gives no induced mass. -/
theorem induced_zero (flow : Flow firstSpace lastSpace) :
    flow.induced (Measure.zero firstSpace) = Measure.zero lastSpace := by
  rw [induced_eq_bind, Measure.zero_bind]

/-- A stage whose potential vanishes gives the zero measure, whatever the later stages weigh. -/
theorem induced_zero_stage {middle : Type u} {middleSpace : Space middle}
    (head : Stage firstSpace middleSpace) (rest : Flow middleSpace lastSpace)
    (vanishes : ∀ pair, head.potential pair = ENNReal.zero) (initial : Measure firstSpace) :
    (stage head rest).induced initial = Measure.zero lastSpace := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_induced _ _ measurable, lintegral_zero_measure]
  have equal : (stage head rest).backward function = fun _ => ENNReal.zero := by
    rw [backward]
    funext input
    have inner : (fun output => ENNReal.mul (head.potential (input, output))
        (rest.backward function output)) = fun _ => ENNReal.zero :=
      funext fun output => by
        show ENNReal.mul (head.potential (input, output)) _ = ENNReal.zero
        rw [vanishes, ENNReal.zero_mul]
    show lintegral (head.proposal input) (fun output => ENNReal.mul
      (head.potential (input, output)) (rest.backward function output)) = ENNReal.zero
    rw [inner, lintegral_zero]
  rw [equal, lintegral_zero]

/-- Reading the last state through a measurable map composes the test with the map. -/
theorem lintegral_readout {γ : Type v} {result : Space γ} (flow : Flow firstSpace lastSpace)
    (initial : Measure firstSpace) {readout : last → γ}
    (readoutMeasurable : MeasurableMap lastSpace result readout) {function : γ → ENNReal}
    (measurable : ENNRealMeasurable result function) :
    lintegral ((flow.induced initial).map readout readoutMeasurable) function =
      lintegral initial (flow.backward fun state => function (readout state)) := by
  rw [lintegral_map _ _ _ measurable,
    lintegral_induced flow initial (measurable.comp readoutMeasurable)]

/-- A population whose expected empirical measure is the induced measure estimates every
nonnegative test without bias. -/
theorem population_test {ι : Type} (lanes : Lanes ι) {flow : Flow firstSpace lastSpace}
    {initial : Measure firstSpace} {population : Measure (populationSpace ι lastSpace)}
    (mean : population.bind (empirical lanes lastSpace) = flow.induced initial)
    {function : last → ENNReal} (measurable : ENNRealMeasurable lastSpace function) :
    lintegral population (fun draws => lintegral (empirical lanes lastSpace draws) function) =
      lintegral initial (flow.backward function) := by
  rw [← Measure.lintegral_bind population (empirical lanes lastSpace) measurable, mean,
    lintegral_induced _ _ measurable]

/-- Its expected mean weight is the evidence. -/
theorem population_evidence {ι : Type} (lanes : Lanes ι) {flow : Flow firstSpace lastSpace}
    {initial : Measure firstSpace} {population : Measure (populationSpace ι lastSpace)}
    (mean : population.bind (empirical lanes lastSpace) = flow.induced initial) :
    lintegral population (fun draws => ENNReal.finite (meanWeight lanes draws)) =
      flow.evidence initial := by
  rw [evidence_eq, ← population_test lanes mean (ENNRealMeasurable.constant lastSpace ENNReal.one)]
  apply lintegral_congr
  intro draws
  rw [lintegral_const, ENNReal.one_mul]
  exact (empirical_mass lanes draws).symm

end Flow

end

end Problib.Inference.FeynmanKac
