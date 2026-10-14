module

public import Problib.QuasiBorel.SFinite.Iteration
public import Problib.QuasiBorel.Measurable.StandardBorel
public import Problib.Measure.Embedding.Retraction
public import Problib.Measure.Kernel.Iteration.Algebra
public import Problib.Measure.Kernel.Precomp
public meta import Trust.Claim

/-!
# Kernel views of positive recursion

A kernel view reads a law family as a transition kernel. It encodes a
standard-Borel input as a point of the family's domain, through a quasi-Borel
morphism, and reads the family's outputs through a measurable map. The view of
every law family is one s-finite kernel: along the standard-Borel retraction
from the reals, the encoding becomes a random element of the domain.

A kernel operator represents a positive map under two views when it is
monotone and commutes with the map at every law family. It acts on kernels
with their s-finite decomposition, because a contextual bind attaches its
source's output to its input. Under a representation, the view of the least
law is the supremum of the operator's fuel, unfolds by one step, and lies below
every kernel that one step keeps below itself. That kernel needs neither a
decomposition nor a law family: the bound is an induction on fuel.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel

public section

universe u v

/-- A kernel with its s-finite decomposition. -/
structure Certified {alpha : Type u} {beta : Type v} (source : Space alpha)
    (target : Space beta) where
  kernel : Kernel source target
  sfinite : IsSFinite kernel

namespace Certified

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- The zero kernel with its decomposition. -/
@[expose, trust_claim] noncomputable def zero (source : Space alpha) (target : Space beta) :
    Certified source target :=
  ⟨Kernel.zero source target, IsSFinite.zero source target⟩

/-- The fuel of a kernel operator: zero, then one more step at each depth. -/
@[expose, trust_claim] noncomputable def fuel
    (op : Certified source target → Certified source target) :
    Nat → Certified source target
  | 0 => zero source target
  | count + 1 => op (fuel op count)

end Certified

end

end Problib.Measure.Kernel

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u v w z s t s2 t2

/-- A reading of law families on `X` and `Y` as kernels from `source` to
`target`: a standard-Borel input encoded into `X` by a quasi-Borel morphism,
and a measurable read of `Y`. -/
structure KernelView (X : Space.{0, u} realSource) (Y : Space.{0, v} realSource)
    {alpha : Type s} {beta : Type t} (source : Problib.Measure.Space alpha)
    (target : Problib.Measure.Space beta) where
  standard : StandardBorel source
  encode : Hom (Space.ofMeasurable Problib.Measure.Real.borel source) X
  read : Y.Carrier → beta
  read_measurable : MeasurableMap Y.toMeasurable target read

namespace KernelView

variable {X : Space.{0, u} realSource} {Y : Space.{0, v} realSource}
  {alpha : Type s} {beta : Type t} {source : Problib.Measure.Space alpha}
  {target : Problib.Measure.Space beta}

/-- The encoding is measurable into the domain's induced measurable space. -/
@[trust_claim] theorem encode_measurable (view : KernelView X Y source target) :
    MeasurableMap source X.toMeasurable view.encode := by
  intro region measurable
  have measured : (Space.ofMeasurable Problib.Measure.Real.borel source).toMeasurable.Measurable
      (Set.preimage view.encode region) :=
    view.encode.toMeasurable measurable
  rw [Space.toMeasurable_of_standardBorel_real view.standard] at measured
  exact measured

/-- A law family read as a kernel. -/
@[expose, trust_claim] noncomputable def apply (view : KernelView X Y source target)
    (f : FamilyHom X Y) : Kernel source target :=
  ((toKernel f).map view.read view.read_measurable).precomp view.encode
    view.encode_measurable

/-- At a measurable set the view is the law's mass on the set's preimage. -/
@[trust_claim] theorem apply_apply (view : KernelView X Y source target) (f : FamilyHom X Y)
    (input : alpha) {set : Set beta} (measurable : target.Measurable set) :
    view.apply f input set = (f (view.encode input)).val (Set.preimage view.read set) := by
  rw [KernelView.apply, Kernel.precomp_apply, Kernel.map_apply,
    Problib.Measure.Measure.map_apply _ _ _ measurable]
  rfl

/-- The empty family reads as the zero kernel. -/
@[trust_claim] theorem apply_zero (view : KernelView X Y source target) :
    view.apply (zeroFamily X Y) = Kernel.zero source target := by
  apply Kernel.ext
  intro input
  change (Problib.Measure.Measure.zero Y.toMeasurable).map view.read view.read_measurable =
    Problib.Measure.Measure.zero target
  exact Problib.Measure.Measure.map_zero _ _

/-- Every law family reads as one s-finite kernel. On a nonempty source, the
retraction of the standard-Borel embedding makes the encoding a random element
of the domain, whose precomposed kernel is s-finite; precomposing back along
the embedding recovers the view. An empty source has only the zero kernel. -/
@[expose, trust_claim] noncomputable def isSFinite (view : KernelView X Y source target)
    (f : FamilyHom X Y) : Kernel.IsSFinite (view.apply f) := by
  classical
  by_cases inhabited : Nonempty alpha
  · have accepted : X.Random (fun seed => view.encode (MeasurableEmbedding.retract
        view.standard.embeddingReal (Classical.choice inhabited) seed)) :=
      view.encode.map_random
        (MeasurableEmbedding.retract_measurable view.standard.embeddingReal _)
    have equal : (((toKernel f).precomp _ (Space.random_measurable accepted)).precomp
        view.standard.embeddingReal.function view.standard.embeddingReal.measurable).map
          view.read view.read_measurable = view.apply f := by
      apply Kernel.ext
      intro input
      simp only [KernelView.apply, Kernel.map_apply, Kernel.precomp_apply,
        MeasurableEmbedding.retract_forward]
    exact equal ▸ ((toKernelPrecompSFinite f accepted).precomp
      view.standard.embeddingReal.function view.standard.embeddingReal.measurable).map
        view.read view.read_measurable
  · have equal : view.apply f = Kernel.zero source target :=
      Kernel.ext fun input => absurd ⟨input⟩ inhabited
    exact equal ▸ Kernel.IsSFinite.zero source target

/-- A law family's view with its decomposition. -/
@[expose, trust_claim] noncomputable def certified (view : KernelView X Y source target)
    (f : FamilyHom X Y) : Kernel.Certified source target :=
  ⟨view.apply f, view.isSFinite f⟩

end KernelView

/-- A kernel operator represents a positive map under an inner and an outer
view when it is monotone and commutes with the map at every law family. -/
structure Represents {U : Space.{0, w} realSource} {V : Space.{0, z} realSource}
    {X : Space.{0, u} realSource} {Y : Space.{0, v} realSource}
    {alpha : Type s} {beta : Type t} {alpha' : Type s2} {beta' : Type t2}
    {source : Problib.Measure.Space alpha} {target : Problib.Measure.Space beta}
    {source' : Problib.Measure.Space alpha'} {target' : Problib.Measure.Space beta'}
    (inner : KernelView X Y source target) (outer : KernelView U V source' target')
    (F : PositiveMap X Y U V)
    (op : Kernel.Certified source target → Kernel.Certified source' target') : Prop where
  monotone : ∀ q r : Kernel.Certified source target, Kernel.le q.kernel r.kernel →
    Kernel.le (op q).kernel (op r).kernel
  commutes : ∀ f, outer.apply (F.operator f) = (op (inner.certified f)).kernel

namespace Represents

variable {U : Space.{0, w} realSource} {V : Space.{0, z} realSource}
  {X : Space.{0, u} realSource} {Y : Space.{0, v} realSource}
  {alpha : Type s} {beta : Type t} {alpha' : Type s2} {beta' : Type t2}
  {source : Problib.Measure.Space alpha} {target : Problib.Measure.Space beta}
  {source' : Problib.Measure.Space alpha'} {target' : Problib.Measure.Space beta'}

/-- A representing operator's kernel does not depend on the decomposition it
is given. -/
@[trust_claim] theorem congr {inner : KernelView X Y source target}
    {outer : KernelView U V source' target'} {F : PositiveMap X Y U V}
    {op : Kernel.Certified source target → Kernel.Certified source' target'}
    (rep : Represents inner outer F op) {q r : Kernel.Certified source target}
    (equal : q.kernel = r.kernel) : (op q).kernel = (op r).kernel := by
  apply Kernel.le_antisymm
  · apply rep.monotone
    rw [equal]
    exact Kernel.le_refl _
  · apply rep.monotone
    rw [equal]
    exact Kernel.le_refl _

variable {view : KernelView X Y source target} {F : PositiveMap X Y X Y}
  {op : Kernel.Certified source target → Kernel.Certified source target}

/-- Each finite unfolding reads as the operator's fuel at the same depth. -/
@[trust_claim] theorem apply_unroll (rep : Represents view view F op) :
    (count : Nat) → view.apply (unroll F count) = (Kernel.Certified.fuel op count).kernel
  | 0 => view.apply_zero
  | count + 1 => by
      show view.apply (F.operator (unroll F count)) = (op (Kernel.Certified.fuel op count)).kernel
      exact (rep.commutes (unroll F count)).trans
        (rep.congr (q := view.certified (unroll F count))
          (r := Kernel.Certified.fuel op count) (apply_unroll rep count))

/-- The least law reads as the supremum of the operator's fuel at every
measurable set. -/
@[trust_claim] theorem least_apply (rep : Represents view view F op) (input : alpha)
    {set : Set beta} (measurable : target.Measurable set) :
    view.apply (least F) input set =
      ENNReal.iSup (fun count => (Kernel.Certified.fuel op count).kernel input set) := by
  rw [view.apply_apply _ _ measurable,
    _root_.Problib.QuasiBorel.SFinite.least_apply F _ (view.read_measurable measurable)]
  congr 1
  funext count
  rw [← rep.apply_unroll count, view.apply_apply _ _ measurable]

/-- The least law's view is one step of the operator applied to itself. -/
@[trust_claim] theorem least_unfold (rep : Represents view view F op) :
    view.apply (least F) = (op (view.certified (least F))).kernel := by
  have commuted := rep.commutes (least F)
  rw [_root_.Problib.QuasiBorel.SFinite.least_unfold F] at commuted
  exact commuted

/-- The least law's view lies below every kernel `q` that one step keeps below
itself from below: whenever a decomposed kernel lies below `q`, so does its
step. `q` needs neither a decomposition nor a law family. -/
@[trust_claim] theorem least_le_of_step (rep : Represents view view F op)
    (q : Kernel source target)
    (step : ∀ r : Kernel.Certified source target, Kernel.le r.kernel q →
      Kernel.le (op r).kernel q) :
    Kernel.le (view.apply (least F)) q := by
  have bounded : ∀ count, Kernel.le (Kernel.Certified.fuel op count).kernel q := by
    intro count
    induction count with
    | zero => exact Kernel.zero_le q
    | succ count induction => exact step _ induction
  intro input set measurable
  rw [rep.least_apply input measurable]
  exact ENNReal.iSup_le (fun count => bounded count input set measurable)

/-- The least law's view lies below every decomposed pre-fixed point. -/
@[trust_claim] theorem least_le_of_prefixed (rep : Represents view view F op)
    (q : Kernel.Certified source target) (prefixed : Kernel.le (op q).kernel q.kernel) :
    Kernel.le (view.apply (least F)) q.kernel :=
  rep.least_le_of_step q.kernel fun r below => Kernel.le_trans (rep.monotone r q below) prefixed

/-- When a monotone operator on all kernels agrees with the representing
operator on decomposed kernels, the least law's view lies below each of its
pre-fixed points. -/
@[trust_claim] theorem least_le_of_total (rep : Represents view view F op)
    (K : Kernel source target → Kernel source target)
    (monotone : ∀ a b, Kernel.le a b → Kernel.le (K a) (K b))
    (agree : ∀ r : Kernel.Certified source target, (op r).kernel = K r.kernel)
    (q : Kernel source target) (prefixed : Kernel.le (K q) q) :
    Kernel.le (view.apply (least F)) q :=
  rep.least_le_of_step q fun r below => by
    rw [agree r]
    exact Kernel.le_trans (monotone _ _ below) prefixed

end Represents

end

end Problib.QuasiBorel.SFinite
