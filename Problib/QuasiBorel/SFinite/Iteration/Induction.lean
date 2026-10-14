module

public import Problib.QuasiBorel.SFinite.Iteration
public import Problib.QuasiBorel.SFinite.Closed
public import Problib.QuasiBorel.SFinite.Mass
public meta import Trust.Claim

/-!
# Fixpoint induction for represented least laws

Two least laws, on any spaces, are compared through their integrals against
paired tests. When one step of each operator keeps the integrals equal at
related points, so do the least laws (`least_agree`), and likewise for a lower
bound (`least_bounds`). The proof is fuel induction on the finite unfoldings,
which both start at the empty law, followed by `least_lintegral`. It asks for
no continuity of the tests and no domain-theoretic object: each observation is
an integral of one fixed test, and `PositiveMap` already carries the continuity
the least law needs.

The step ranges over every pair of s-finite families, so it is a statement
about the operators' readings, not about the laws they reach. It is built from
one rule per constructor (`Keeps`). The rule for bind asks that each paired
output test pull back, through the two continuations, to a paired test of the
intermediate results. That closure is what makes a test class compositional:
mass alone is not closed under it, since a continuation may branch on the
result. Agreement on mass or on one expectation is read off agreement on a
closed class, never composed on its own.

Two closed classes are given. `decoded` pairs every measurable test with its
composite through a measurable decoding, and its agreement is equality of the
decoded laws. `weighted` pairs every measurable test with the same test
weighed by a carried weight, which is a weighted sampler's identity.

A recursion whose meaning is a least family read at root points becomes a
probability law only after that reading. `probability_of_agree` transfers mass
one through the literal unweighted pair `(1, 1)`, from one related point to
another, and a consumer applies it at its root points.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Real (ENNReal)

universe u v w z t s t' s'

variable {X : Space.{0, u} realSource} {Y : Space.{0, v} realSource}
  {X' : Space.{0, w} realSource} {Y' : Space.{0, z} realSource}

/-- Paired tests on two result spaces. -/
abbrev Tests (Y : Space.{0, v} realSource) (Y' : Space.{0, z} realSource) :=
  (Y.Carrier → ENNReal) → (Y'.Carrier → ENNReal) → Prop

/-- At related points, paired tests have equal integrals. -/
@[expose] def Agree (related : X.Carrier → X'.Carrier → Prop) (tests : Tests Y Y')
    (f : FamilyHom X Y) (g : FamilyHom X' Y') : Prop :=
  ∀ x x', related x x' → ∀ t t', tests t t' →
    lintegral (f x).val t = lintegral (g x').val t'

/-- At related points, each test of the first family integrates below its
partner in the second. -/
@[expose] def Bounds (related : X.Carrier → X'.Carrier → Prop) (tests : Tests Y Y')
    (f : FamilyHom X Y) (g : FamilyHom X' Y') : Prop :=
  ∀ x x', related x x' → ∀ t t', tests t t' →
    ENNReal.le (lintegral (f x).val t) (lintegral (g x').val t')

section Induction

variable (F : PositiveMap X Y X Y) (G : PositiveMap X' Y' X' Y')
  (related : X.Carrier → X'.Carrier → Prop) (tests : Tests Y Y')

@[trust_claim] theorem unroll_agree
    (step : ∀ f g, Agree related tests f g → Agree related tests (F.operator f) (G.operator g))
    (n : Nat) : Agree related tests (unroll F n) (unroll G n) := by
  induction n with
  | zero =>
      intro x x' _ t t' _
      exact (lintegral_zero_measure t).trans (lintegral_zero_measure t').symm
  | succ n ih => exact step _ _ ih

/-- Fixpoint induction: what one step of each operator keeps, the least laws
have. -/
@[trust_claim] theorem least_agree
    (step : ∀ f g, Agree related tests f g → Agree related tests (F.operator f) (G.operator g)) :
    Agree related tests (least F) (least G) := by
  intro x x' r t t' paired
  rw [least_lintegral, least_lintegral]
  exact congrArg ENNReal.iSup
    (funext fun n => unroll_agree F G related tests step n x x' r t t' paired)

@[trust_claim] theorem unroll_bounds
    (step : ∀ f g, Bounds related tests f g → Bounds related tests (F.operator f) (G.operator g))
    (n : Nat) : Bounds related tests (unroll F n) (unroll G n) := by
  induction n with
  | zero =>
      intro x x' _ t t' _
      rw [show lintegral (unroll F 0 x).val t = ENNReal.zero from lintegral_zero_measure t]
      exact ENNReal.zero_le _
  | succ n ih => exact step _ _ ih

/-- Fixpoint induction for a lower bound on the second least law. -/
@[trust_claim] theorem least_bounds
    (step : ∀ f g, Bounds related tests f g → Bounds related tests (F.operator f) (G.operator g)) :
    Bounds related tests (least F) (least G) := by
  intro x x' r t t' paired
  rw [least_lintegral, least_lintegral]
  exact ENNReal.iSup_le fun n => ENNReal.le_trans
    (unroll_bounds F G related tests step n x x' r t t' paired)
    (ENNReal.le_iSup (fun k => lintegral (unroll G k x').val t') n)

end Induction

/-! ### One rule per constructor -/

variable {U : Space.{0, s} realSource} {V : Space.{0, t} realSource}
  {U' : Space.{0, s'} realSource} {V' : Space.{0, t'} realSource}
  {related : X.Carrier → X'.Carrier → Prop} {tests : Tests Y Y'}

/-- One step of two positive maps keeps agreement: families that agree on the
continuation's relation and tests give laws that agree on the output's. -/
@[expose] def Keeps (related : X.Carrier → X'.Carrier → Prop) (tests : Tests Y Y')
    (inner : U.Carrier → U'.Carrier → Prop) (output : Tests V V')
    (F : PositiveMap X Y U V) (G : PositiveMap X' Y' U' V') : Prop :=
  ∀ f g, Agree related tests f g → Agree inner output (F.operator f) (G.operator g)

variable {inner : U.Carrier → U'.Carrier → Prop} {output : Tests V V'}

@[trust_claim] theorem Keeps.constant {f : FamilyHom U V} {g : FamilyHom U' V'}
    (agree : Agree inner output f g) :
    Keeps related tests inner output (PositiveMap.constant X Y f) (PositiveMap.constant X' Y' g) :=
  fun _ _ _ => agree

@[trust_claim] theorem Keeps.precomp {W : Space.{0, s} realSource} {W' : Space.{0, s'} realSource}
    {F : PositiveMap X Y U V} {G : PositiveMap X' Y' U' V'}
    (keeps : Keeps related tests inner output F G) (e : Hom W U) (e' : Hom W' U')
    {before : W.Carrier → W'.Carrier → Prop} (maps : ∀ q q', before q q' → inner (e q) (e' q')) :
    Keeps related tests before output (F.precomp e) (G.precomp e') :=
  fun f g agree q q' r => keeps f g agree _ _ (maps q q' r)

/-- A call reads both continuations at related captured points. -/
@[trust_claim] theorem Keeps.call (e : Hom U X) (e' : Hom U' X')
    (captured : ∀ q q', inner q q' → related (e q) (e' q')) :
    Keeps related tests inner tests (PositiveMap.call (Y := Y) e) (PositiveMap.call (Y := Y') e') :=
  fun _ _ agree q q' r => agree _ _ (captured q q' r)

/-- Related sum points select the same branch with related payloads. -/
@[expose] def SumRelated {W : Space.{0, s} realSource} {W' : Space.{0, s'} realSource}
    (left : U.Carrier → U'.Carrier → Prop) (right : W.Carrier → W'.Carrier → Prop) :
    (Space.sum U W).Carrier → (Space.sum U' W').Carrier → Prop
  | .inl q, .inl q' => left q q'
  | .inr q, .inr q' => right q q'
  | _, _ => False

@[trust_claim] theorem Keeps.copair {W : Space.{0, s} realSource} {W' : Space.{0, s'} realSource}
    {F : PositiveMap X Y U V} {G : PositiveMap X' Y' U' V'}
    {F' : PositiveMap X Y W V} {G' : PositiveMap X' Y' W' V'}
    {right : W.Carrier → W'.Carrier → Prop}
    (first : Keeps related tests inner output F G) (second : Keeps related tests right output F' G') :
    Keeps related tests (SumRelated inner right) output (F.copair F') (G.copair G') := by
  intro f g agree q q' r t t' paired
  match q, q', r with
  | .inl q, .inl q', r => exact first f g agree q q' r t t' paired
  | .inr q, .inr q', r => exact second f g agree q q' r t t' paired

/-- Contextual bind. `pullback` is the closure of the intermediate tests under
the continuations: at related environments, each paired output test integrates
through the two continuations to a paired intermediate test. -/
@[trust_claim] theorem Keeps.bindContext {Z : Space.{0, t} realSource} {Z' : Space.{0, t'} realSource}
    {middle : Tests V V'} {final : Tests Z Z'}
    {F : PositiveMap X Y U V} {G : PositiveMap X' Y' U' V'}
    {K : PositiveMap X Y (Space.product U V) Z} {K' : PositiveMap X' Y' (Space.product U' V') Z'}
    (source : Keeps related tests inner middle F G)
    (measurable : ∀ t t', final t t' →
      ENNRealMeasurable Z.toMeasurable t ∧ ENNRealMeasurable Z'.toMeasurable t')
    (pullback : ∀ f g, Agree related tests f g → ∀ q q', inner q q' → ∀ t t', final t t' →
      middle (fun v => lintegral (K.operator f (q, v)).val t)
        (fun v' => lintegral (K'.operator g (q', v')).val t')) :
    Keeps related tests inner final (F.bindContext K) (G.bindContext K') := by
  intro f g agree q q' r t t' paired
  rw [PositiveMap.bindContext_operator, PositiveMap.bindContext_operator, bindContext_apply,
    bindContext_apply, bind_val, bind_val, Measure.lintegral_bind _ _ (measurable t t' paired).1,
    Measure.lintegral_bind _ _ (measurable t t' paired).2]
  exact source f g agree q q' r _ _ (pullback f g agree q q' r t t' paired)

/-! ### Decoded laws -/

/-- Every measurable test, paired with its composite through a decoding. -/
@[expose] def decoded (decode : Hom Y' Y) : Tests Y Y' :=
  fun t t' => ENNRealMeasurable Y.toMeasurable t ∧ t' = fun y => t (decode y)

theorem decoded_measurable (decode : Hom Y' Y) {t t'} (paired : decoded decode t t') :
    ENNRealMeasurable Y.toMeasurable t ∧ ENNRealMeasurable Y'.toMeasurable t' := by
  obtain ⟨measurable, rfl⟩ := paired
  exact ⟨measurable, ENNRealMeasurable.comp measurable decode.toMeasurable⟩

/-- Agreement on decoded tests is equality of laws after the decoding. -/
@[trust_claim] theorem eq_of_agree_decoded (decode : Hom Y' Y) {f : FamilyHom X Y}
    {g : FamilyHom X' Y'} (agree : Agree related (decoded decode) f g) {x x'}
    (r : related x x') : f x = map decode (g x') := by
  apply Law.ext
  apply Measure.ext
  intro A hA
  rw [map_val, Measure.map_apply _ _ _ @hA, apply_eq_lintegral_indicator _ @hA,
    apply_eq_lintegral_indicator _ (by exact decode.toMeasurable @hA)]
  exact agree x x' r _ _ ⟨ENNRealMeasurable.indicator @hA (ENNRealMeasurable.constant _ _), rfl⟩

/-- Equal laws after the decoding agree on decoded tests. -/
@[trust_claim] theorem agree_decoded_of_eq (decode : Hom Y' Y) {f : FamilyHom X Y}
    {g : FamilyHom X' Y'} (equal : ∀ x x', related x x' → f x = map decode (g x')) :
    Agree related (decoded decode) f g := by
  rintro x x' r t _ ⟨measurable, rfl⟩
  rw [equal x x' r, map_val, lintegral_map _ _ _ measurable]

/-- A bound on decoded tests bounds every measurable set. -/
@[trust_claim] theorem le_of_bounds_decoded (decode : Hom Y' Y) {f : FamilyHom X Y}
    {g : FamilyHom X' Y'} (bounds : Bounds related (decoded decode) f g) {x x'}
    (r : related x x') {A : Set Y.Carrier} (hA : Y.toMeasurable.Measurable A) :
    ENNReal.le ((f x).val A) ((map decode (g x')).val A) := by
  rw [map_val, Measure.map_apply _ _ _ @hA, apply_eq_lintegral_indicator (f x).val @hA,
    apply_eq_lintegral_indicator _ (by exact decode.toMeasurable @hA)]
  exact bounds x x' r _ _ ⟨ENNRealMeasurable.indicator @hA (ENNRealMeasurable.constant _ _), rfl⟩

/-- Decoded tests pull back through a bind whose delivered continuation
respects the decoding: it is related at every environment whose bound value
decodes to the source's. -/
@[trust_claim] theorem decoded_pullback {Z : Space.{0, t} realSource} {Z' : Space.{0, t'} realSource}
    (decode : Hom V' V) (decodeOut : Hom Z' Z)
    {K : PositiveMap X Y (Space.product U V) Z} {K' : PositiveMap X' Y' (Space.product U' V') Z'}
    (body : Keeps related tests
      (fun (p : (Space.product U V).Carrier) (p' : (Space.product U' V').Carrier) =>
        inner p.1 p'.1 ∧ p.2 = decode p'.2) (decoded decodeOut) K K') :
    ∀ f g, Agree related tests f g → ∀ q q', inner q q' → ∀ t t', decoded decodeOut t t' →
      decoded decode (fun v => lintegral (K.operator f (q, v)).val t)
        (fun v' => lintegral (K'.operator g (q', v')).val t') := by
  intro f g agree q q' r t t' paired
  refine ⟨Kernel.lintegral_measurable (toKernel (Space.curry (K.operator f) q)) paired.1, ?_⟩
  funext v'
  exact (body f g agree (q, decode v') (q', v') ⟨r, rfl⟩ t t' paired).symm

/-! ### Mass, as a projection of agreement -/

/-- The constant test integrates to mass. -/
theorem lintegral_one (law : Law Y) :
    lintegral law.val (fun _ => ENNReal.one) = mass Y law := by
  rw [lintegral_const, ENNReal.one_mul]
  rfl

/-- When the tests hold the mass pair, agreeing families have equal mass. -/
@[trust_claim] theorem mass_eq_of_agree {f : FamilyHom X Y} {g : FamilyHom X' Y'}
    (unit : tests (fun _ => ENNReal.one) (fun _ => ENNReal.one))
    (agree : Agree related tests f g) {x x'} (r : related x x') :
    mass Y (f x) = mass Y' (g x') := by
  rw [← lintegral_one, ← lintegral_one]
  exact agree x x' r _ _ unit

/-- When the tests hold the mass pair, a bound bounds the mass. -/
@[trust_claim] theorem mass_le_of_bounds {f : FamilyHom X Y} {g : FamilyHom X' Y'}
    (unit : tests (fun _ => ENNReal.one) (fun _ => ENNReal.one))
    (bounds : Bounds related tests f g) {x x'} (r : related x x') :
    ENNReal.le (mass Y (f x)) (mass Y' (g x')) := by
  rw [← lintegral_one, ← lintegral_one]
  exact bounds x x' r _ _ unit

/-- Mass one transfers between related points through the literal unweighted
pair `(1, 1)`. The weighted pair `(1, w)` equates the source's mass with the
delivered recursion's expected weight, and a law of mass one half carrying
weight two meets that without being a probability law. -/
@[trust_claim] theorem probability_of_agree (F : PositiveMap X Y X Y) (G : PositiveMap X' Y' X' Y')
    (unit : tests (fun _ => ENNReal.one) (fun _ => ENNReal.one))
    (step : ∀ f g, Agree related tests f g → Agree related tests (F.operator f) (G.operator g))
    {x x'} (r : related x x') (ready : Measure.IsProbability (least F x).val) :
    Measure.IsProbability (least G x').val :=
  ⟨(mass_eq_of_agree unit (least_agree F G related tests step) r).symm.trans ready.univ_eq_one⟩

/-! ### Weighted samplers -/

/-- A weighted sampler's tests: every measurable test of a law, paired with
the same test weighed by the carried weight, `(y, w) ↦ w · t y`.

The class holds every measurable test, because a bind integrates its
continuation first: a step on `t` asks for agreement on the section
`y ↦ ∫ t d(k y)`, which is again a measurable test, and a smaller class is
not closed under it (`weighted_pullback`). -/
@[expose] def weighted (Y : Space.{0, v} realSource) : Tests Y (Space.product Y weightSpace) :=
  fun t t' => ENNRealMeasurable Y.toMeasurable t ∧ t' = fun pair => ENNReal.mul pair.2 (t pair.1)

theorem weighted_measurable {t t'} (paired : weighted Y t t') :
    ENNRealMeasurable Y.toMeasurable t ∧
      ENNRealMeasurable (Space.product Y weightSpace).toMeasurable t' := by
  obtain ⟨measurable, rfl⟩ := paired
  exact ⟨measurable, (weight_measurable (Space.second Y weightSpace)).mul
    (ENNRealMeasurable.comp measurable (Space.first Y weightSpace).toMeasurable)⟩

/-- Weighted tests pull back through a weighted bind. The delivered
continuation `K'` reads only the drawn value, through `K''`, and multiplies
its own weight by the carried one. -/
@[trust_claim] theorem weighted_pullback {Z : Space.{0, t} realSource}
    {K : PositiveMap X Y (Space.product U V) Z}
    {K' : PositiveMap X' Y' (Space.product U' (Space.product V weightSpace))
      (Space.product Z weightSpace)}
    {K'' : PositiveMap X' Y' (Space.product U' V) (Space.product Z weightSpace)}
    (body : Keeps related tests
      (fun (p : (Space.product U V).Carrier) (p' : (Space.product U' V).Carrier) =>
        inner p.1 p'.1 ∧ p.2 = p'.2) (weighted Z) K K'')
    (multiplies : ∀ g q' v w t, ENNRealMeasurable Z.toMeasurable t →
      lintegral (K'.operator g (q', (v, w))).val (fun pair => ENNReal.mul pair.2 (t pair.1)) =
        ENNReal.mul w
          (lintegral (K''.operator g (q', v)).val (fun pair => ENNReal.mul pair.2 (t pair.1)))) :
    ∀ f g, Agree related tests f g → ∀ q q', inner q q' → ∀ t t', weighted Z t t' →
      weighted V (fun v => lintegral (K.operator f (q, v)).val t)
        (fun pair => lintegral (K'.operator g (q', pair)).val t') := by
  rintro f g agree q q' r t _ ⟨measurable, rfl⟩
  refine ⟨Kernel.lintegral_measurable (toKernel (Space.curry (K.operator f) q)) measurable, ?_⟩
  funext pair
  obtain ⟨v, w⟩ := pair
  rw [multiplies g q' v w t measurable]
  exact congrArg (ENNReal.mul w) (body f g agree (q, v) (q', v) ⟨r, rfl⟩ t _ ⟨measurable, rfl⟩).symm

/-- Fixpoint induction for a weighted sampler: a delivered recursion whose
step keeps the weighted tests weighs every measurable test as the source's
least law integrates it. It gives no readiness: see `probability_of_agree`. -/
@[trust_claim] theorem least_weighted (F : PositiveMap X Y X Y)
    (G : PositiveMap X' (Space.product Y weightSpace) X' (Space.product Y weightSpace))
    (step : ∀ f g, Agree related (weighted Y) f g →
      Agree related (weighted Y) (F.operator f) (G.operator g))
    {x x'} (r : related x x') {t : Y.Carrier → ENNReal}
    (measurable : ENNRealMeasurable Y.toMeasurable t) :
    lintegral (least F x).val t =
      lintegral (least G x').val (fun pair => ENNReal.mul pair.2 (t pair.1)) :=
  least_agree F G related (weighted Y) step x x' r _ _ ⟨measurable, rfl⟩

end

end Problib.QuasiBorel.SFinite
