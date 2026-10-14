module

public import Problib.QuasiBorel.SFinite.Counting
public import Problib.QuasiBorel.SFinite.Closed
public import Problib.QuasiBorel.SFinite.Weight
public import Problib.QuasiBorel.Sum
public import Problib.Measure.Kernel.Supremum
public meta import Trust.Claim

/-!
# Positive recursion on represented law families

A positive map carries the represented increments of its output as well as
monotonicity and continuity on cumulative chains. Summing the recursively
constructed increments gives a quasi-Borel morphism before taking any measure
limit. The resulting law is the least pre-fixed point and the supremum of its
zero-based finite unfoldings. Contextual bind partitions pairs of paths by their
maximum depth, so both children may read the recursive continuation.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u v w z t

abbrev FamilyHom (X : Space.{0, u} realSource) (Y : Space.{0, v} realSource) :=
  Hom X (object Y)

variable {X : Space.{0, u} realSource} {Y : Space.{0, v} realSource}
  {U : Space.{0, w} realSource} {V : Space.{0, z} realSource}

/-- Pointwise measure order, tested on the induced measurable sets. -/
@[expose, implicit_reducible] def Below (f g : FamilyHom X Y) : Prop :=
  ∀ x A, Y.toMeasurable.Measurable A → ENNReal.le ((f x).val A) ((g x).val A)

@[trust_claim] theorem below_refl (f : FamilyHom X Y) : Below f f :=
  fun _ _ _ => ENNReal.le_refl _

@[trust_claim] theorem below_trans {f g h : FamilyHom X Y}
    (fg : Below f g) (gh : Below g h) : Below f h :=
  fun x A hA => ENNReal.le_trans (fg x A @hA) (gh x A @hA)

@[trust_claim] theorem below_antisymm {f g : FamilyHom X Y}
    (fg : Below f g) (gf : Below g f) : f = g := by
  apply Hom.ext
  intro x
  apply Law.ext
  apply Measure.ext
  intro A hA
  exact ENNReal.le_antisymm (fg x A @hA) (gf x A @hA)

/-- The empty family is available even when either carrier is empty. -/
@[expose] noncomputable def zeroFamily (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) : FamilyHom X Y :=
  Hom.constant X (object Y) (zero Y)

@[trust_claim] theorem zeroFamily_below (f : FamilyHom X Y) :
    Below (zeroFamily X Y) f := by
  intro x A _
  change ENNReal.le ((zero Y).val A) _
  rw [zero_val, Measure.zero_apply]
  exact ENNReal.zero_le _

/-- Binary addition uses the same represented countable sum as the limit. -/
@[expose] noncomputable def addFamily (f g : FamilyHom X Y) : FamilyHom X Y :=
  sum (fun n => match n with
    | 0 => f
    | 1 => g
    | _ + 2 => zeroFamily X Y)

@[trust_claim] theorem addFamily_val (f g : FamilyHom X Y) (x : X.Carrier) :
    (addFamily f g x).val = Measure.add (f x).val (g x).val := by
  apply Measure.ext
  intro A hA
  rw [Measure.add_apply_measurable _ _ @hA]
  change (Measure.sum _ ) A = _
  rw [Measure.sum_apply _ @hA]
  have equal : (fun n => ((match n with
      | 0 => f
      | 1 => g
      | _ + 2 => zeroFamily X Y) x).val A) =
      ENNReal.pair ((f x).val A) ((g x).val A) := by
    funext n
    match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => exact Measure.zero_apply A
  rw [equal, ENNReal.tsum_pair]

@[trust_claim] theorem addFamily_zero_left (f : FamilyHom X Y) :
    addFamily (zeroFamily X Y) f = f := by
  apply Hom.ext
  intro x
  apply Law.ext
  rw [addFamily_val]
  exact Measure.zero_add _

@[trust_claim] theorem addFamily_zero_right (f : FamilyHom X Y) :
    addFamily f (zeroFamily X Y) = f := by
  apply Hom.ext
  intro x
  apply Law.ext
  rw [addFamily_val]
  exact Measure.add_zero _

@[trust_claim] theorem addFamily_assoc (f g h : FamilyHom X Y) :
    addFamily (addFamily f g) h = addFamily f (addFamily g h) := by
  apply Hom.ext
  intro x
  apply Law.ext
  rw [addFamily_val, addFamily_val, addFamily_val, addFamily_val]
  exact Measure.add_assoc _ _ _

@[trust_claim] theorem addFamily_mono {f g h k : FamilyHom X Y}
    (fg : Below f g) (hk : Below h k) : Below (addFamily f h) (addFamily g k) := by
  intro x A hA
  rw [addFamily_val, addFamily_val, Measure.add_apply_measurable _ _ @hA,
    Measure.add_apply_measurable _ _ @hA]
  exact ENNReal.add_le_add (fg x A @hA) (hk x A @hA)

/-- Finite cumulative sums of represented increments. -/
@[expose] noncomputable def prefixSum (d : Nat → FamilyHom X Y) : Nat → FamilyHom X Y
  | 0 => zeroFamily X Y
  | n + 1 => addFamily (prefixSum d n) (d n)

@[trust_claim] theorem prefix_congr {d e : Nat → FamilyHom X Y} (n : Nat)
    (equal : ∀ k, k < n → d k = e k) : prefixSum d n = prefixSum e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [prefixSum, prefixSum, ih (fun k hk => equal k (Nat.lt_trans hk (Nat.lt_succ_self n))),
        equal n (Nat.lt_succ_self n)]

@[trust_claim] theorem prefix_apply (d : Nat → FamilyHom X Y) (n : Nat)
    (x : X.Carrier) {A : Set Y.Carrier} (hA : Y.toMeasurable.Measurable A) :
    (prefixSum d n x).val A = ENNReal.partialSum (fun k => (d k x).val A) n := by
  induction n with
  | zero => exact Measure.zero_apply A
  | succ n ih =>
      rw [prefixSum, addFamily_val, Measure.add_apply_measurable _ _ @hA, ih,
        ENNReal.partialSum]

@[trust_claim] theorem prefix_le_succ (d : Nat → FamilyHom X Y) (n : Nat) :
    Below (prefixSum d n) (prefixSum d (n+1)) := by
  intro x A hA
  rw [prefix_apply d n x @hA, prefix_apply d (n+1) x @hA]
  exact ENNReal.partialSum_step _ n

@[trust_claim] theorem sum_apply_measurable (d : Nat → FamilyHom X Y)
    (x : X.Carrier) {A : Set Y.Carrier} (hA : Y.toMeasurable.Measurable A) :
    (sum d x).val A = ENNReal.tsum (fun n => (d n x).val A) :=
  Measure.sum_apply _ @hA

@[trust_claim] theorem sum_eq_prefix_sup (d : Nat → FamilyHom X Y)
    (x : X.Carrier) {A : Set Y.Carrier} (hA : Y.toMeasurable.Measurable A) :
    (sum d x).val A = ENNReal.iSup (fun n => (prefixSum d n x).val A) := by
  rw [sum_apply_measurable d x @hA]
  unfold ENNReal.tsum
  exact congrArg ENNReal.iSup (funext fun n => (prefix_apply d n x @hA).symm)

@[trust_claim] theorem lintegral_sum (d : Nat → FamilyHom X Y) (x : X.Carrier)
    (f : Y.Carrier → ENNReal) :
    lintegral (sum d x).val f = ENNReal.tsum (fun n => lintegral (d n x).val f) :=
  Problib.Measure.lintegral_sum _ f

@[trust_claim] theorem prefix_lintegral (d : Nat → FamilyHom X Y) (n : Nat)
    (x : X.Carrier) (f : Y.Carrier → ENNReal) :
    lintegral (prefixSum d n x).val f =
      ENNReal.partialSum (fun k => lintegral (d k x).val f) n := by
  induction n with
  | zero => exact lintegral_zero_measure f
  | succ n ih => rw [prefixSum, addFamily_val, lintegral_add_measure, ih, ENNReal.partialSum]

/-- A positive expression gives represented output increments causally and
preserves limits of represented cumulative chains. Its output spaces may differ
from the spaces of the distinguished recursive continuation. -/
structure PositiveMap (X : Space.{0, u} realSource) (Y : Space.{0, v} realSource)
    (U : Space.{0, w} realSource) (V : Space.{0, z} realSource) where
  operator : FamilyHom X Y → FamilyHom U V
  monotone : ∀ f g, Below f g → Below (operator f) (operator g)
  action : (Nat → FamilyHom X Y) → Nat → FamilyHom U V
  causal : ∀ d e n, (∀ k, k < n → d k = e k) → action d n = action e n
  prefix_eq : ∀ d n, operator (prefixSum d n) = prefixSum (action d) (n+1)
  continuous : ∀ d u A, V.toMeasurable.Measurable A →
    (operator (sum d) u).val A = ENNReal.iSup (fun n => (operator (prefixSum d n) u).val A)

/-- Finite unfoldings start at the empty law. -/
@[expose] noncomputable def unroll (F : PositiveMap X Y X Y) : Nat → FamilyHom X Y
  | 0 => zeroFamily X Y
  | n + 1 => F.operator (unroll F n)

/-- Depth n consults only earlier increments; later entries are padded by zero. -/
@[expose] noncomputable def increments (F : PositiveMap X Y X Y) (n : Nat) :
    FamilyHom X Y :=
  F.action (fun k => if _earlier : k < n then increments F k else zeroFamily X Y) n
termination_by n

@[trust_claim] theorem increments_eq_action (F : PositiveMap X Y X Y) (n : Nat) :
    increments F n = F.action (increments F) n := by
  unfold increments
  apply F.causal
  intro k hk
  simp [hk]

@[trust_claim] theorem unroll_eq_prefix (F : PositiveMap X Y X Y) (n : Nat) :
    unroll F n = prefixSum (increments F) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unroll, ih, F.prefix_eq]
      apply prefix_congr
      intro k _
      exact (increments_eq_action F k).symm

@[trust_claim] theorem unroll_mono (F : PositiveMap X Y X Y) (n : Nat) :
    Below (unroll F n) (unroll F (n+1)) := by
  rw [unroll_eq_prefix, unroll_eq_prefix]
  exact prefix_le_succ _ n

/-- Summing represented increments supplies the law and its family morphism. -/
@[expose] noncomputable def least (F : PositiveMap X Y X Y) : FamilyHom X Y :=
  sum (increments F)

@[trust_claim] theorem least_apply (F : PositiveMap X Y X Y) (x : X.Carrier)
    {A : Set Y.Carrier} (hA : Y.toMeasurable.Measurable A) :
    (least F x).val A = ENNReal.iSup (fun n => (unroll F n x).val A) := by
  rw [least, sum_eq_prefix_sup _ x @hA]
  exact congrArg ENNReal.iSup (funext fun n =>
    congrArg (fun f : FamilyHom X Y => (f x).val A) (unroll_eq_prefix F n).symm)

@[trust_claim] theorem least_unfold (F : PositiveMap X Y X Y) :
    F.operator (least F) = least F := by
  apply below_antisymm
  · intro x A hA
    rw [least, F.continuous _ x A @hA, sum_eq_prefix_sup _ x @hA]
    apply ENNReal.iSup_le
    intro n
    rw [F.prefix_eq]
    have equal : prefixSum (F.action (increments F)) (n+1) = prefixSum (increments F) (n+1) :=
      prefix_congr _ (fun k _ => (increments_eq_action F k).symm)
    rw [equal]
    exact ENNReal.le_iSup (fun k => (prefixSum (increments F) k x).val A) (n+1)
  · intro x A hA
    rw [least_apply F x @hA]
    apply ENNReal.iSup_le
    intro n
    cases n with
    | zero => exact zeroFamily_below _ x A @hA
    | succ n =>
        apply F.monotone _ _ _ x A @hA
        intro y B hB
        rw [least_apply F y @hB]
        exact ENNReal.le_iSup (fun k => (unroll F k y).val B) n

@[trust_claim] theorem least_least (F : PositiveMap X Y X Y) (q : FamilyHom X Y)
    (prefixed : Below (F.operator q) q) : Below (least F) q := by
  have bounded : ∀ n, Below (unroll F n) q := by
    intro n
    induction n with
    | zero => exact zeroFamily_below q
    | succ n ih => exact below_trans (F.monotone _ _ ih) prefixed
  intro x A hA
  rw [least_apply F x @hA]
  exact ENNReal.iSup_le (fun n => bounded n x A @hA)

/-- The integral limit holds even for tests that are not measurable. -/
@[trust_claim] theorem least_lintegral (F : PositiveMap X Y X Y) (x : X.Carrier)
    (f : Y.Carrier → ENNReal) :
    lintegral (least F x).val f = ENNReal.iSup (fun n => lintegral (unroll F n x).val f) := by
  rw [least, lintegral_sum]
  unfold ENNReal.tsum
  apply congrArg ENNReal.iSup
  funext n
  rw [unroll_eq_prefix, prefix_lintegral]

@[trust_claim] theorem unroll_precomp {X' : Space.{0, w} realSource}
    (F : PositiveMap X Y X Y) (G : PositiveMap X' Y X' Y) (e : Hom X' X)
    (compatible : ∀ f, G.operator (Hom.comp f e) = Hom.comp (F.operator f) e)
    (n : Nat) : unroll G n = Hom.comp (unroll F n) e := by
  induction n with
  | zero => apply Hom.ext; intro x; rfl
  | succ n ih => rw [unroll, ih, compatible]; rfl

@[trust_claim] theorem least_precomp {X' : Space.{0, w} realSource}
    (F : PositiveMap X Y X Y) (G : PositiveMap X' Y X' Y) (e : Hom X' X)
    (compatible : ∀ f, G.operator (Hom.comp f e) = Hom.comp (F.operator f) e) :
    least G = Hom.comp (least F) e := by
  apply Hom.ext
  intro x
  apply Law.ext
  apply Measure.ext
  intro A hA
  simp only [Hom.comp_apply]
  rw [least_apply G x @hA, least_apply F (e x) @hA]
  exact congrArg ENNReal.iSup (funext fun n =>
    congrArg (fun f : FamilyHom X' Y => (f x).val A) (unroll_precomp F G e compatible n))


@[trust_claim] theorem toKernel_addFamily (f g : FamilyHom X Y) :
    toKernel (addFamily f g) = Kernel.add (toKernel f) (toKernel g) := by
  apply Kernel.ext
  intro x
  exact addFamily_val f g x

@[trust_claim] theorem toKernel_prefix (d : Nat → FamilyHom X Y) (n : Nat) :
    toKernel (prefixSum d n) = Kernel.prefixSum (fun k => toKernel (d k)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixSum, toKernel_addFamily, ih, Kernel.prefixSum]

@[trust_claim] theorem toKernel_injective {f g : FamilyHom X Y}
    (equal : toKernel f = toKernel g) : f = g := by
  apply Hom.ext
  intro x
  apply Law.ext
  exact congrArg (fun k : Kernel X.toMeasurable Y.toMeasurable => k x) equal

@[trust_claim] theorem below_toKernel_iff (f g : FamilyHom X Y) :
    Below f g ↔ Kernel.le (toKernel f) (toKernel g) := Iff.rfl

namespace PositiveMap

/-- The continuity certificate identifies the output kernel limit, without
claiming a global s-finite certificate for arbitrary induced QBS kernels. -/
@[trust_claim] theorem toKernel_sum (F : PositiveMap X Y U V)
    (d : Nat → FamilyHom X Y) :
    toKernel (F.operator (sum d)) =
      Kernel.iSupIncreasing (fun n => toKernel (F.operator (prefixSum d n)))
        (fun n => (below_toKernel_iff _ _).mp (F.monotone _ _ (prefix_le_succ d n))) := by
  apply Kernel.ext_measurable
  intro x A hA
  rw [Kernel.iSupIncreasing_apply_measurable _ _ x @hA]
  exact F.continuous d x A @hA

/-- An independent child contributes its law only at depth zero. -/
@[expose] noncomputable def constant (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) (f : FamilyHom U V) : PositiveMap X Y U V where
  operator := fun _ => f
  monotone := fun _ _ _ => below_refl f
  action := fun _ n => if n = 0 then f else zeroFamily U V
  causal := by intro _ _ _ _; rfl
  prefix_eq := by
    intro d n
    induction n with
    | zero => exact (addFamily_zero_left f).symm
    | succ n ih =>
        change f = addFamily
          (prefixSum (fun k => if k = 0 then f else zeroFamily U V) (n+1))
          (zeroFamily U V)
        rw [addFamily_zero_right]
        exact ih
  continuous := by intro _ _ _ _; exact (ENNReal.iSup_const _).symm

/-- A recursive call shifts input increments by one output depth. -/
@[expose] noncomputable def identity (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) : PositiveMap X Y X Y where
  operator := id
  monotone := fun _ _ h => h
  action := fun d n => match n with
    | 0 => zeroFamily X Y
    | k+1 => d k
  causal := by
    intro d e n h
    cases n with
    | zero => rfl
    | succ n => exact h n (Nat.lt_succ_self n)
  prefix_eq := by
    intro d n
    induction n with
    | zero => exact (addFamily_zero_left _).symm
    | succ n ih =>
        change addFamily (prefixSum d n) (d n) =
          addFamily (prefixSum (fun k => match k with
            | 0 => zeroFamily X Y
            | k+1 => d k) (n+1)) (d n)
        have prior : prefixSum d n = prefixSum (fun k => match k with
            | 0 => zeroFamily X Y
            | k+1 => d k) (n+1) := ih
        rw [prior]
  continuous := fun d x A hA => sum_eq_prefix_sup d x @hA

/-- Source precomposition acts on each represented increment. -/
@[expose] noncomputable def precomp {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (e : Hom W U) : PositiveMap X Y W V where
  operator := fun f => Hom.comp (F.operator f) e
  monotone := fun f g h x A hA => F.monotone f g h (e x) A @hA
  action := fun d n => Hom.comp (F.action d n) e
  causal := by intro d e' n h; rw [F.causal d e' n h]
  prefix_eq := by
    intro d n
    rw [F.prefix_eq]
    apply Hom.ext
    intro x
    apply Law.ext
    apply Measure.ext
    intro A hA
    simp only [Hom.comp_apply]
    rw [prefix_apply _ _ (e x) @hA, prefix_apply _ _ x @hA]
    rfl
  continuous := fun d x A hA => F.continuous d (e x) A @hA

/-- The distinguished continuation is read at a captured environment. -/
@[expose] noncomputable def call (e : Hom U X) : PositiveMap X Y U Y :=
  (identity X Y).precomp e

/-- Output pushforward preserves represented cumulative chains. -/
@[expose] noncomputable def map {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (e : Hom V W) : PositiveMap X Y U W where
  operator := fun f => Hom.comp (SFinite.map e) (F.operator f)
  monotone := by
    intro f g h x A hA
    simp only [Hom.comp_apply]
    rw [map_val, map_val, Measure.map_apply _ _ _ @hA, Measure.map_apply _ _ _ @hA]
    exact F.monotone f g h x _ (by exact e.toMeasurable @hA)
  action := fun d n => Hom.comp (SFinite.map e) (F.action d n)
  causal := by intro d e' n h; rw [F.causal d e' n h]
  prefix_eq := by
    intro d n
    rw [F.prefix_eq]
    apply Hom.ext
    intro x
    apply Law.ext
    apply Measure.ext
    intro A hA
    simp only [Hom.comp_apply]
    rw [map_val, Measure.map_apply _ _ _ @hA,
      prefix_apply _ _ x (by exact e.toMeasurable @hA), prefix_apply _ _ x @hA]
    apply congrArg (fun values => ENNReal.partialSum values (n+1))
    funext k
    simp only [Hom.comp_apply]
    rw [map_val, Measure.map_apply _ _ _ @hA]
  continuous := by
    intro d x A hA
    simp only [Hom.comp_apply]
    rw [map_val, Measure.map_apply _ _ _ @hA, F.continuous d x _ (by exact e.toMeasurable @hA)]
    apply congrArg ENNReal.iSup
    funext n
    rw [map_val, Measure.map_apply _ _ _ @hA]

/-- Ordinary bind of two positive expressions. Both may read the distinguished
continuation; the diagonal increment counts every pair once. -/
@[expose] noncomputable def compose {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (G : PositiveMap X Y V W) : PositiveMap X Y U W where
  operator := fun f => Hom.comp (extend (G.operator f)) (F.operator f)
  monotone := by
    intro f g h
    apply (below_toKernel_iff _ _).mpr
    rw [toKernel_extend_comp, toKernel_extend_comp]
    exact Kernel.le_trans
      (Kernel.comp_le_comp_left ((below_toKernel_iff _ _).mp (F.monotone f g h))
        (toKernel (G.operator f)))
      (Kernel.comp_le_comp_right (toKernel (F.operator g))
        ((below_toKernel_iff _ _).mp (G.monotone f g h)))
  action := fun d n => addFamily
    (Hom.comp (extend (G.action d n)) (prefixSum (F.action d) n))
    (Hom.comp (extend (prefixSum (G.action d) (n+1))) (F.action d n))
  causal := by
    intro d e n h
    have firstPrefix : prefixSum (F.action d) n = prefixSum (F.action e) n :=
      prefix_congr n (fun k hk => F.causal d e k
        (fun j hj => h j (Nat.lt_trans hj hk)))
    have secondPrefix : prefixSum (G.action d) (n+1) = prefixSum (G.action e) (n+1) :=
      prefix_congr (n+1) (fun k hk => G.causal d e k
        (fun j hj => h j (Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hk))))
    rw [firstPrefix, secondPrefix, F.causal d e n h, G.causal d e n h]
  prefix_eq := by
    intro d n
    rw [F.prefix_eq, G.prefix_eq]
    apply toKernel_injective
    rw [toKernel_extend_comp, toKernel_prefix, toKernel_prefix, toKernel_prefix,
      Kernel.comp_prefixSum_eq_prefixSum_diagonalPrefixIncrement]
    apply congrArg (fun paths => Kernel.prefixSum paths (n+1))
    funext k
    rw [toKernel_addFamily, toKernel_extend_comp, toKernel_extend_comp,
      toKernel_prefix, toKernel_prefix]
    rfl
  continuous := by
    intro d x A hA
    have limit := Kernel.comp_iSupIncreasing_diagonal
      (fun n => toKernel (F.operator (prefixSum d n)))
      (fun n => (below_toKernel_iff _ _).mp (F.monotone _ _ (prefix_le_succ d n)))
      (fun n => toKernel (G.operator (prefixSum d n)))
      (fun n => (below_toKernel_iff _ _).mp (G.monotone _ _ (prefix_le_succ d n)))
    rw [← F.toKernel_sum d, ← G.toKernel_sum d] at limit
    have evaluated := congrArg (fun k => k x A) limit
    rw [Kernel.iSupIncreasing_apply_measurable _ _ x @hA] at evaluated
    exact evaluated

/-- Keep the environment with each output using QBS strength. No equality
between induced product sigma algebras is required. -/
@[expose] noncomputable def attach (F : PositiveMap X Y U V) :
    PositiveMap X Y U (Space.product U V) where
  operator := fun f => Hom.comp (strength U V) (Space.pair (Hom.identity U) (F.operator f))
  monotone := by
    intro f g h x A hA
    change ENNReal.le ((strength U V (x, F.operator f x)).val A)
      ((strength U V (x, F.operator g x)).val A)
    rw [strength_val, strength_val, Measure.map_apply _ _ _ @hA, Measure.map_apply _ _ _ @hA]
    exact F.monotone f g h x _ (by exact (Space.pairLeft U V x).toMeasurable @hA)
  action := fun d n => Hom.comp (strength U V) (Space.pair (Hom.identity U) (F.action d n))
  causal := by intro d e n h; rw [F.causal d e n h]
  prefix_eq := by
    intro d n
    rw [F.prefix_eq]
    apply Hom.ext
    intro x
    apply Law.ext
    apply Measure.ext
    intro A hA
    change (strength U V (x, prefixSum (F.action d) (n+1) x)).val A = _
    rw [strength_val, Measure.map_apply _ _ _ @hA,
      prefix_apply _ _ x (by exact (Space.pairLeft U V x).toMeasurable @hA), prefix_apply _ _ x @hA]
    apply congrArg (fun values => ENNReal.partialSum values (n+1))
    funext k
    change _ = (strength U V (x, F.action d k x)).val A
    rw [strength_val, Measure.map_apply _ _ _ @hA]
  continuous := by
    intro d x A hA
    change (strength U V (x, F.operator (sum d) x)).val A =
      ENNReal.iSup (fun n => (strength U V (x, F.operator (prefixSum d n) x)).val A)
    rw [strength_val, Measure.map_apply _ _ _ @hA,
      F.continuous d x _ (by exact (Space.pairLeft U V x).toMeasurable @hA)]
    apply congrArg ENNReal.iSup
    funext n
    rw [strength_val, Measure.map_apply _ _ _ @hA]

/-- Contextual bind retains the environment for the continuation child. -/
@[expose] noncomputable def bindContext {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (G : PositiveMap X Y (Space.product U V) W) :
    PositiveMap X Y U W := F.attach.compose G

@[trust_claim] theorem bindContext_operator {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (G : PositiveMap X Y (Space.product U V) W)
    (f : FamilyHom X Y) :
    (F.bindContext G).operator f = SFinite.bindContext (F.operator f) (G.operator f) := by
  apply Hom.ext
  intro x
  apply Law.ext
  change (bind (strength U V (x, F.operator f x)) (G.operator f)).val = _
  rw [bind_val, strength_val, Measure.bind_map, SFinite.bindContext_apply, bind_val]
  rfl

/-- Independent case selection sends each depth to the selected branch. -/
@[expose] noncomputable def copair {W : Space.{0, t} realSource}
    (F : PositiveMap X Y U V) (G : PositiveMap X Y W V) :
    PositiveMap X Y (Space.sum U W) V where
  operator := fun f => Space.copair (F.operator f) (G.operator f)
  monotone := by
    intro f g h x A hA
    cases x with
    | inl x => exact F.monotone f g h x A @hA
    | inr x => exact G.monotone f g h x A @hA
  action := fun d n => Space.copair (F.action d n) (G.action d n)
  causal := by intro d e n h; rw [F.causal d e n h, G.causal d e n h]
  prefix_eq := by
    intro d n
    apply Hom.ext
    intro x
    apply Law.ext
    apply Measure.ext
    intro A hA
    cases x with
    | inl x =>
        have eq := congrArg (fun f : FamilyHom U V => (f x).val A) (F.prefix_eq d n)
        rw [prefix_apply _ _ x @hA] at eq
        exact eq.trans (prefix_apply (X := Space.sum U W)
          (fun k => Space.copair (F.action d k) (G.action d k)) (n+1)
          (Space.inl U W x) @hA).symm
    | inr x =>
        have eq := congrArg (fun f : FamilyHom W V => (f x).val A) (G.prefix_eq d n)
        rw [prefix_apply _ _ x @hA] at eq
        exact eq.trans (prefix_apply (X := Space.sum U W)
          (fun k => Space.copair (F.action d k) (G.action d k)) (n+1)
          (Space.inr U W x) @hA).symm
  continuous := by
    intro d x A hA
    cases x with
    | inl x => exact F.continuous d x A @hA
    | inr x => exact G.continuous d x A @hA

/-- Pointwise countable sums carry the supplied positive decompositions. The
summand indexing is fixed independently of the recursive continuation. -/
@[expose] noncomputable def countableSum (F : Nat → PositiveMap X Y U V) :
    PositiveMap X Y U V where
  operator := fun f => sum (fun k => (F k).operator f)
  monotone := by
    intro f g h x A hA
    rw [sum_apply_measurable _ x @hA, sum_apply_measurable _ x @hA]
    exact ENNReal.tsum_le_tsum (fun k => (F k).monotone f g h x A @hA)
  action := fun d n => sum (fun k => (F k).action d n)
  causal := by
    intro d e n h
    apply congrArg sum
    funext k
    exact (F k).causal d e n h
  prefix_eq := by
    intro d n
    apply Hom.ext
    intro x
    apply Law.ext
    apply Measure.ext
    intro A hA
    rw [sum_apply_measurable _ x @hA, prefix_apply _ _ x @hA]
    have left : (fun k => ((F k).operator (prefixSum d n) x).val A) =
        (fun k => ENNReal.partialSum (fun j => ((F k).action d j x).val A) (n+1)) := by
      funext k
      rw [(F k).prefix_eq, prefix_apply _ _ x @hA]
    have right : (fun j => (sum (fun k => (F k).action d j) x).val A) =
        (fun j => ENNReal.tsum (fun k => ((F k).action d j x).val A)) := by
      funext j
      exact sum_apply_measurable _ x @hA
    rw [left, right]
    exact (ENNReal.partialSum_tsum (fun j k => ((F k).action d j x).val A) (n+1)).symm
  continuous := by
    intro d x A hA
    rw [sum_apply_measurable _ x @hA]
    have left : (fun k => ((F k).operator (sum d) x).val A) =
        (fun k => ENNReal.iSup (fun n => ((F k).operator (prefixSum d n) x).val A)) := by
      funext k
      exact (F k).continuous d x A @hA
    have right : (fun n => (sum (fun k => (F k).operator (prefixSum d n)) x).val A) =
        (fun n => ENNReal.tsum (fun k => ((F k).operator (prefixSum d n) x).val A)) := by
      funext n
      exact sum_apply_measurable _ x @hA
    rw [left, right]
    exact ENNReal.tsum_iSup (fun n k => ((F k).operator (prefixSum d n) x).val A)
      (fun n k => (F k).monotone _ _ (prefix_le_succ d n) x A @hA)

/-- Binary choice uses the countable constructor with two nonzero summands. -/
@[expose] noncomputable def add (F G : PositiveMap X Y U V) : PositiveMap X Y U V :=
  countableSum (fun n => match n with
    | 0 => F
    | 1 => G
    | _+2 => constant X Y (zeroFamily U V))

@[trust_claim] theorem add_operator (F G : PositiveMap X Y U V) (f : FamilyHom X Y) :
    (F.add G).operator f = addFamily (F.operator f) (G.operator f) := by
  unfold add countableSum addFamily
  apply congrArg sum
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | _+2 => rfl

/-- An independent family of scores contributes only at depth zero. -/
@[expose] noncomputable def independentScore (X : Space.{0, u} realSource)
    (Y : Space.{0, v} realSource) (density : Hom U weightSpace) :
    PositiveMap X Y U (Space.terminal realSource) :=
  constant X Y (Hom.comp score density)

/-- An independent density may reweight every output path of a positive body. -/
@[expose] noncomputable def weight (F : PositiveMap X Y U V) (density : Hom V weightSpace) :
    PositiveMap X Y U V :=
  F.compose (constant X Y
    (Hom.comp (weightedPoint V) (Space.pair density (Hom.identity V))))

@[trust_claim] theorem weight_operator (F : PositiveMap X Y U V)
    (density : Hom V weightSpace) (f : FamilyHom X Y) :
    (F.weight density).operator f = Hom.comp (SFinite.weight density) (F.operator f) := rfl

end PositiveMap

/-- Successful positive readings with the same operator have the same fuel. -/
@[trust_claim] theorem unroll_congr_operator (F G : PositiveMap X Y X Y)
    (equal : F.operator = G.operator) (n : Nat) : unroll F n = unroll G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unroll, unroll, equal, ih]

/-- The least law depends on the operator, not its chosen increment certificate. -/
@[trust_claim] theorem least_congr_operator (F G : PositiveMap X Y X Y)
    (equal : F.operator = G.operator) : least F = least G := by
  apply Hom.ext
  intro x
  apply Law.ext
  apply Measure.ext
  intro A hA
  rw [least_apply F x @hA, least_apply G x @hA]
  exact congrArg ENNReal.iSup (funext fun n =>
    congrArg (fun f : FamilyHom X Y => (f x).val A) (unroll_congr_operator F G equal n))

/-- Mass one requires exactly that the supremum of approximant masses is one. -/
@[trust_claim] theorem least_probability_iff (F : PositiveMap X Y X Y) (x : X.Carrier) :
    Measure.IsProbability (least F x).val ↔
      ENNReal.iSup (fun n => (unroll F n x).val Set.univ) = ENNReal.one := by
  constructor
  · intro h
    exact (least_apply F x (by exact Y.toMeasurable.univ)).symm.trans h.univ_eq_one
  · intro h
    exact ⟨(least_apply F x (by exact Y.toMeasurable.univ)).trans h⟩

end

end Problib.QuasiBorel.SFinite
