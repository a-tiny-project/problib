module

public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Product.Parallel
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Kernel.Measurable.Section
public import Problib.Measure.Pi
import Problib.Measure.Kernel.Product.Transport
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Measurability.Extended
import Problib.Measure.Kernel.Measurable

set_option autoImplicit false

/-! # Finite products of kernels

`Kernel.pair` samples two s-finite kernels of one input independently, and at
each input it is `Measure.prod` of the two (`pair_apply`). `Kernel.finProduct`
folds `pair` over `Fin extent`, one kernel per lane, into a kernel on
`Space.pi fun _ : Fin extent => target`. This is the single finite-product
abstraction in problib: multinomial ancestors, conditional SMC and the density
of a vectorized draw all read it.

The fold splits at lane `0` by definition (`finProduct_succ_apply`). It splits
at every lane: the product, read as the chosen lane and the others in order, is
`Measure.prod` of that lane's measure and the product of the others
(`finProduct_split`). Inserting a lane back inverts the split
(`laneInsert_split`), so a product whose lane is pinned to a point integrates
the other lanes with that point inserted (`lintegral_finProduct_pinned`). Reading one lane of a product of probability kernels reads
that lane's kernel (`lintegral_finProduct_coordinate`), and reading two distinct
lanes reads their two kernels independently (`lintegral_finProduct_pair`). The
marginal identities need probability kernels: at a finite kernel of mass other
than one, the other lanes do not integrate away.
-/

namespace Problib.Measure

open Problib.Real

universe u v w x

namespace Kernel

variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {head : Space β} {tail : Space γ}

public section

/-! ### Independent pairs -/

/-- Run a kernel of the input and keep the input after the draw. -/
@[expose] noncomputable def attached (kernel : Kernel source head) (finite : IsSFinite kernel) :
    Kernel source (Space.product head source) :=
  (kernel.attach finite).map (fun pair => (pair.2, pair.1)) (Space.swap_measurable _ _)

noncomputable def IsSFinite.attached {kernel : Kernel source head} (finite : IsSFinite kernel) :
    IsSFinite (kernel.attached finite) :=
  finite.attach.map _ (Space.swap_measurable _ _)

/-- An attached kernel's draw at an input, with that input kept beside it. -/
theorem attached_apply (kernel : Kernel source head) (finite : IsSFinite kernel) (input : α) :
    kernel.attached finite input =
      (kernel input).map (fun value => (value, input))
        (Space.pair_measurable (MeasurableMap.identity head) (vertical_map_measurable input)) := by
  change (((kernel input).map _ _).map _ _) = _
  rw [Measure.map_comp]

/-- Attaching keeps the order of two kernels at every measurable set. -/
theorem attached_le_attached {first second : Kernel source head}
    (firstFinite : IsSFinite first) (secondFinite : IsSFinite second)
    (below : ∀ input set, head.Measurable set →
      ENNReal.le (first input set) (second input set)) :
    ∀ input set, (Space.product head source).Measurable set →
      ENNReal.le (first.attached firstFinite input set) (second.attached secondFinite input set) := by
  intro input set measurable
  rw [attached_apply, attached_apply, Measure.map_apply _ _ _ measurable,
    Measure.map_apply _ _ _ measurable]
  exact below input _ (Space.pair_measurable (MeasurableMap.identity head)
    (vertical_map_measurable input) measurable)

/-- Run a kernel of the input beside an already drawn first value, keeping
both draws. -/
@[expose] noncomputable def joined (kernel : Kernel source tail) (finite : IsSFinite kernel) :
    Kernel (Space.product head source) (Space.product head tail) :=
  ((kernel.precomp (fun pair => pair.2) (Space.second_measurable _ _)).attached
      (finite.precomp _ (Space.second_measurable _ _))).map
    (fun pair => (pair.2.1, pair.1)) (by measurability)

theorem joined_apply (kernel : Kernel source tail) (finite : IsSFinite kernel)
    (input : β × α) :
    joined (head := head) kernel finite input =
      (kernel input.2).map (fun value => (input.1, value))
        (pair_left_measurable (source := head) (target := tail) input.1) := by
  change ((((kernel input.2).map _ _).map _ _).map _ _) = _
  rw [Measure.map_comp, Measure.map_comp]

/-- Sample two kernels of one input independently and keep both draws. -/
@[expose] noncomputable def pair (left : Kernel source head) (leftFinite : IsSFinite left)
    (right : Kernel source tail) (rightFinite : IsSFinite right) :
    Kernel source (Space.product head tail) :=
  (left.attached leftFinite).comp (joined right rightFinite)

noncomputable def IsSFinite.pair {left : Kernel source head} (leftFinite : IsSFinite left)
    {right : Kernel source tail} (rightFinite : IsSFinite right) :
    IsSFinite (Kernel.pair left leftFinite right rightFinite) :=
  leftFinite.attached.comp ((rightFinite.precomp _ (Space.second_measurable _ _)).attached.map _
    (by measurability))

/-- The independent pair at one input is the product of its two measures. -/
theorem pair_apply (left : Kernel source head) (leftFinite : IsSFinite left)
    (right : Kernel source tail) (rightFinite : IsSFinite right) (input : α) :
    pair left leftFinite right rightFinite input =
      Measure.prod (left input) (right input) (rightFinite.measure input) := by
  change (((left.attached leftFinite) input).bind (joined right rightFinite)) = _
  change ((((left input).map _ _).map _ _).bind (joined right rightFinite)) = _
  rw [Measure.map_comp, Measure.bind_map, Measure.prod, Measure.semiproduct]
  apply congrArg (Measure.bind (left input))
  apply Kernel.ext
  intro value
  rw [Kernel.precomp_apply, joined_apply, Kernel.attach_apply, Kernel.const_apply]

/-- A pair of probability kernels is a probability kernel. -/
theorem pair_markov {left : Kernel source head} (leftFinite : IsSFinite left)
    {right : Kernel source tail} (rightFinite : IsSFinite right)
    (leftMarkov : ∀ input, Measure.IsProbability (left input))
    (rightMarkov : ∀ input, Measure.IsProbability (right input)) (input : α) :
    Measure.IsProbability (pair left leftFinite right rightFinite input) := by
  rw [pair_apply, Measure.prod, Measure.semiproduct]
  refine (leftMarkov input).bind _ fun value => ?_
  rw [Kernel.attach_apply, Kernel.const_apply]
  exact (rightMarkov input).map _ _

/-- `parallel` is `pair` of its two kernels, each read at its own coordinate.
So problib has one kernel product, and `parallel` is its instance on a product
source. -/
theorem parallel_eq_pair {σ : Type u} {τ : Type v} {first : Space σ} {second : Space τ}
    (leftKernel : Kernel first head) (rightKernel : Kernel second tail)
    (leftFinite : ∀ input, Measure.IsFinite (leftKernel input))
    (rightFinite : ∀ input, Measure.IsFinite (rightKernel input)) :
    parallel leftKernel rightKernel leftFinite rightFinite =
      pair (leftKernel.precomp Prod.fst (Space.first_measurable first second))
        (IsSFinite.ofFiniteFibers fun input => leftFinite input.1)
        (rightKernel.precomp Prod.snd (Space.second_measurable first second))
        (IsSFinite.ofFiniteFibers fun input => rightFinite input.2) := by
  apply Kernel.ext
  intro input
  rw [parallel_apply, pair_apply]
  exact Measure.prod_certificate_irrelevant _ _ _ _

/-! ### The finite fold -/

/-- A pair of a value and a tuple is a successor tuple. -/
theorem cons_measurable (target : Space β) (extent : Nat) :
    MeasurableMap (Space.product target (Space.pi fun _ : Fin extent => target))
      (Space.pi fun _ : Fin (extent + 1) => target)
      (fun pair => Fin.cases pair.1 pair.2) := by
  refine Space.pi_measurable fun coordinate => ?_
  induction coordinate using Fin.cases with
  | zero => exact Space.first_measurable _ _
  | succ position =>
      have reads : (fun pair : β × (Fin extent → β) =>
            Fin.cases pair.1 pair.2 position.succ) = fun pair => pair.2 position := by
        funext pair
        simp
      rw [reads]
      intro region regionMeasurable
      exact MeasurableMap.comp
        (Space.coordinate_measurable (fun _ : Fin extent => target) position)
        (Space.second_measurable target (Space.pi fun _ : Fin extent => target))
        regionMeasurable

/-- One kernel per lane of `Fin extent`, sampled independently, with its
s-finiteness. The two are built together because each step's product needs the
previous step's witness. -/
noncomputable def finProductBundle {target : Space β} :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
      (∀ lane, IsSFinite (family lane)) →
        Σ kernel : Kernel source (Space.pi fun _ : Fin extent => target), IsSFinite kernel
  | 0, _, _ => ⟨deterministic (fun _ lane => lane.elim0)
      (Space.pi_measurable fun lane => lane.elim0), IsSFinite.deterministic _ _⟩
  | extent + 1, family, finite =>
      let rest := finProductBundle extent (fun lane => family lane.succ) fun lane => finite lane.succ
      ⟨(pair (family 0) (finite 0) rest.1 rest.2).map
          (fun pair => Fin.cases pair.1 pair.2) (cons_measurable target extent),
        ((finite 0).pair rest.2).map _ (cons_measurable target extent)⟩

/-- One kernel per lane of `Fin extent`, sampled independently. -/
@[expose] noncomputable def finProduct {target : Space β} (extent : Nat)
    (family : Fin extent → Kernel source target) (finite : ∀ lane, IsSFinite (family lane)) :
    Kernel source (Space.pi fun _ : Fin extent => target) :=
  (finProductBundle extent family finite).1

/-- A finite product of s-finite kernels is s-finite. -/
noncomputable def IsSFinite.finProduct {target : Space β} (extent : Nat)
    (family : Fin extent → Kernel source target) (finite : ∀ lane, IsSFinite (family lane)) :
    IsSFinite (Kernel.finProduct extent family finite) :=
  (finProductBundle extent family finite).2

variable {target : Space β}

/-- The lane-`0` split, by definition. -/
theorem finProduct_succ_apply (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, IsSFinite (family lane)) (input : α) :
    finProduct (extent + 1) family finite input =
      (Measure.prod (family 0 input)
          (finProduct extent (fun lane => family lane.succ) (fun lane => finite lane.succ) input)
          ((IsSFinite.finProduct extent _ fun lane => finite lane.succ).measure input)).map
        (fun pair lane => Fin.cases pair.1 pair.2 lane) (cons_measurable target extent) := by
  change (pair _ _ _ _).map _ _ input = _
  rw [Kernel.map_apply, pair_apply]
  rfl

/-- A finite product of probability kernels is a probability kernel. -/
theorem finProduct_markov :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
    (finite : ∀ lane, IsSFinite (family lane)) →
    (∀ lane input, Measure.IsProbability (family lane input)) → (input : α) →
    Measure.IsProbability (finProduct extent family finite input)
  | 0, _, _, _, input => Measure.IsProbability.dirac _ _
  | extent + 1, family, finite, markov, input => by
      change Measure.IsProbability (((pair _ _ _ _).map _ _) input)
      rw [Kernel.map_apply]
      exact (pair_markov _ _ (markov 0)
        (finProduct_markov extent _ _ fun lane => markov lane.succ) input).map _ _

/-- A product of two measures equal to Diracs is the Dirac at the pair. -/
theorem prod_eq_dirac {first : β} {second : γ} {leftMeasure : Measure head}
    {rightMeasure : Measure tail} (leftEqual : leftMeasure = Measure.dirac head first)
    (rightEqual : rightMeasure = Measure.dirac tail second)
    (rightFinite : Measure.SFinite rightMeasure) :
    Measure.prod leftMeasure rightMeasure rightFinite =
      Measure.dirac (Space.product head tail) (first, second) := by
  subst leftEqual
  subst rightEqual
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.prod_apply _ _ _ setMeasurable,
    lintegral_dirac head first (integrand := fun input =>
      Measure.dirac tail second (Set.preimage (fun value => (input, value)) set))
      (section_apply_measurable
      (Kernel.const head (Measure.dirac tail second))
      (IsSFinite.const head rightFinite) setMeasurable),
    Measure.dirac_apply _ _ (pair_left_measurable (source := head) first setMeasurable),
    Measure.dirac_apply _ _ setMeasurable]
  rfl

/-- A finite product of kernels that are Diracs at one input is the Dirac at
the tuple of their points. -/
theorem finProduct_dirac :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
    (finite : ∀ lane, IsSFinite (family lane)) → {input : α} →
    {values : Fin extent → β} → (∀ lane, family lane input = Measure.dirac target (values lane)) →
    finProduct extent family finite input =
      Measure.dirac (Space.pi fun _ : Fin extent => target) values
  | 0, _, _, input, values, _ => by
      show Measure.dirac (Space.pi fun _ : Fin 0 => target) (fun lane => lane.elim0) = _
      exact congrArg _ (funext fun lane => lane.elim0)
  | extent + 1, family, finite, input, values, lanes => by
      rw [finProduct_succ_apply, prod_eq_dirac (lanes 0)
        (finProduct_dirac extent _ _ (values := fun lane => values lane.succ)
          fun lane => lanes lane.succ), Measure.map_dirac]
      exact congrArg _ (funext fun lane => by cases lane using Fin.cases <;> rfl)

/-- The product reads its factors only through their kernels, never through
their s-finite witnesses, and pointwise, at inputs of any two sources. -/
theorem finProduct_congr_at {δ : Type x} {origin : Space δ} :
    (extent : Nat) → (left : Fin extent → Kernel source target) →
    (leftFinite : ∀ lane, IsSFinite (left lane)) →
    (right : Fin extent → Kernel origin target) → (rightFinite : ∀ lane, IsSFinite (right lane)) →
    (input : α) → (other : δ) → (∀ lane, left lane input = right lane other) →
    finProduct extent left leftFinite input = finProduct extent right rightFinite other
  | 0, _, _, _, _, _, _, _ => rfl
  | extent + 1, left, leftFinite, right, rightFinite, input, other, equal => by
      rw [finProduct_succ_apply, finProduct_succ_apply]
      apply congrArg (fun measure => Measure.map measure _ (cons_measurable target extent))
      apply Measure.ext
      intro region measurable
      rw [Measure.prod_apply _ _ _ measurable, Measure.prod_apply _ _ _ measurable, equal 0,
        finProduct_congr_at extent _ _ _ _ input other fun lane => equal lane.succ]

/-- Pushing every lane forward along one map pushes the product forward
entrywise. -/
theorem finProduct_map_apply {image : Space γ} (function : β → γ)
    (measurable : MeasurableMap target image function) :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
    (finite : ∀ lane, IsSFinite (family lane)) →
    (mappedFinite : ∀ lane, IsSFinite ((family lane).map function measurable)) → (input : α) →
    finProduct extent (fun lane => (family lane).map function measurable) mappedFinite input =
      (finProduct extent family finite input).map (fun point lane => function (point lane))
        (Space.pi_measurable fun lane =>
          MeasurableMap.comp measurable
            (Space.coordinate_measurable (fun _ : Fin extent => target) lane))
  | 0, family, finite, mappedFinite, input => by
      rw [finProduct_dirac 0 _ mappedFinite (values := fun lane => lane.elim0)
          fun lane => lane.elim0,
        finProduct_dirac 0 family finite (values := fun lane => lane.elim0)
          fun lane => lane.elim0, Measure.map_dirac]
      exact congrArg _ (funext fun lane => lane.elim0)
  | extent + 1, family, finite, mappedFinite, input => by
      have tailMeasurable : MeasurableMap (Space.pi fun _ : Fin extent => target)
          (Space.pi fun _ : Fin extent => image) (fun point lane => function (point lane)) :=
        Space.pi_measurable fun lane =>
          MeasurableMap.comp measurable
            (Space.coordinate_measurable (fun _ : Fin extent => target) lane)
      have rest := finProduct_map_apply function measurable extent (fun lane => family lane.succ)
        (fun lane => finite lane.succ) (fun lane => mappedFinite lane.succ) input
      rw [finProduct_succ_apply, finProduct_succ_apply, Kernel.map_apply,
        Measure.prod_congr_right _ _
          (((IsSFinite.finProduct extent _ fun lane => finite lane.succ).measure input).map
            _ tailMeasurable) rest,
        ← Measure.prod_map _ _ _ _ _ measurable tailMeasurable, Measure.map_comp,
        Measure.map_comp]
      exact Measure.map_congr_function _ _ _
        (funext fun pair => funext fun lane => by cases lane using Fin.cases <;> rfl)

/-! ### Splitting at a lane -/

/-- The lanes other than `lane`, in order: `laneSkip lane j` is `j` below `lane`
and `j + 1` from it on. -/
@[expose] def laneSkip {extent : Nat} (lane : Fin (extent + 1)) (position : Fin extent) :
    Fin (extent + 1) :=
  if position.val < lane.val then ⟨position.val, Nat.lt_succ_of_lt position.isLt⟩
  else ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩

theorem laneSkip_ne {extent : Nat} (lane : Fin (extent + 1)) (position : Fin extent) :
    laneSkip lane position ≠ lane := by
  unfold laneSkip
  split <;> intro equal <;> have := congrArg Fin.val equal <;> simp at this <;> omega

theorem laneSkip_zero {extent : Nat} (position : Fin extent) :
    laneSkip 0 position = position.succ := by
  unfold laneSkip
  split
  · rename_i below
    simp at below
  · rfl

theorem laneSkip_succ_zero {extent : Nat} (lane : Fin (extent + 1)) :
    laneSkip lane.succ (0 : Fin (extent + 1)) = 0 := by
  unfold laneSkip
  split
  · apply Fin.ext
    simp
  · rename_i above
    simp at above

theorem laneSkip_succ_succ {extent : Nat} (lane : Fin (extent + 1)) (position : Fin extent) :
    laneSkip lane.succ position.succ = (laneSkip lane position).succ := by
  apply Fin.ext
  unfold laneSkip
  split <;> split <;> simp_all [Fin.val_succ] <;> omega

/-- Skipping a successor lane of a tuple with a new head keeps the head and
skips the lane below it in the rest. -/
private theorem laneSkip_succ_cons {extent : Nat} (lane : Fin (extent + 1)) (first : β)
    (table : Fin (extent + 1) → β) :
    (fun position : Fin (extent + 1) => (Fin.cases first table (laneSkip lane.succ position) : β)) =
      fun position => Fin.cases first (fun other : Fin extent => table (laneSkip lane other)) position := by
  funext position
  induction position using Fin.cases with
  | zero =>
      rw [laneSkip_succ_zero]
      rfl
  | succ position =>
      rw [laneSkip_succ_succ]
      rfl

/-- Read a tuple as one lane and the others in order. -/
@[expose] def laneSplit {extent : Nat} (lane : Fin (extent + 1)) (table : Fin (extent + 1) → β) :
    β × (Fin extent → β) :=
  (table lane, fun position => table (laneSkip lane position))

theorem laneSplit_measurable {extent : Nat} (lane : Fin (extent + 1)) :
    MeasurableMap (Space.pi fun _ : Fin (extent + 1) => target)
      (Space.product target (Space.pi fun _ : Fin extent => target)) (laneSplit lane) :=
  Space.pair_measurable (Space.coordinate_measurable _ lane)
    (Space.pi_reindex (fun _ : Fin (extent + 1) => target) (laneSkip lane))

/-- Splitting at lane zero is the product's own head and tail. -/
private theorem lintegral_split_zero (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, IsSFinite (family lane)) (input : α)
    {function : β × (Fin extent → β) → ENNReal}
    (functionMeasurable : ENNRealMeasurable
      (Space.product target (Space.pi fun _ : Fin extent => target)) function) :
    lintegral (finProduct (extent + 1) family finite input) (fun table => function (laneSplit 0 table)) =
      lintegral (family 0 input) fun value =>
        lintegral (finProduct extent (fun position => family (laneSkip 0 position))
          (fun position => finite (laneSkip 0 position)) input) fun rest => function (value, rest) := by
  have splitMeasurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target)
      (fun table => function (laneSplit 0 table)) :=
    ENNRealMeasurable.comp functionMeasurable (laneSplit_measurable 0)
  rw [finProduct_succ_apply extent family finite input,
    lintegral_map _ _ (cons_measurable target extent) splitMeasurable,
    lintegral_prod _ _ _ (ENNRealMeasurable.comp splitMeasurable (cons_measurable target extent)),
    finProduct_congr_at extent (fun position => family (laneSkip 0 position)) _
      (fun position => family position.succ) (fun position => finite position.succ) input input
      fun position => by rw [laneSkip_zero]]
  apply lintegral_congr
  intro value
  apply lintegral_congr
  intro rest
  simp only [laneSplit, laneSkip_zero, Fin.cases_zero, Fin.cases_succ]

/-- The lane-split lemma, in integral form: integrating a function of one lane
and the others in order integrates that lane's measure against the product of
the others. -/
theorem lintegral_finProduct_split (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, IsSFinite (family lane)) (lane : Fin (extent + 1)) (input : α)
    {function : β × (Fin extent → β) → ENNReal}
    (functionMeasurable : ENNRealMeasurable
      (Space.product target (Space.pi fun _ : Fin extent => target)) function) :
    lintegral (finProduct (extent + 1) family finite input) (fun table => function (laneSplit lane table)) =
      lintegral (family lane input) fun value =>
        lintegral (finProduct extent (fun position => family (laneSkip lane position))
          (fun position => finite (laneSkip lane position)) input) fun rest => function (value, rest) := by
  induction extent with
  | zero =>
      induction lane using Fin.cases with
      | zero => exact lintegral_split_zero 0 family finite input functionMeasurable
      | succ position => exact position.elim0
  | succ extent smaller =>
      induction lane using Fin.cases with
      | zero => exact lintegral_split_zero (extent + 1) family finite input functionMeasurable
      | succ lane =>
          -- Take lane zero off the product and exchange it past the tail, so that
          -- the hypothesis splits the tail at `lane` with lane zero integrated inside.
          have splitMeasurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1 + 1) => target)
              (fun table => function (laneSplit lane.succ table)) :=
            ENNRealMeasurable.comp functionMeasurable (laneSplit_measurable lane.succ)
          have headMeasurable : ENNRealMeasurable
              (Space.product target (Space.pi fun _ : Fin extent => target))
              (fun value => lintegral (family 0 input) fun first =>
                function (value.1, fun position => Fin.cases first value.2 position)) :=
            by
              have jointMeasurable := ENNRealMeasurable.comp functionMeasurable
                (Space.pair_measurable
                  (MeasurableMap.comp (Space.first_measurable target (Space.pi fun _ : Fin extent => target))
                    (Space.first_measurable
                      (Space.product target (Space.pi fun _ : Fin extent => target)) target))
                  (MeasurableMap.comp (cons_measurable target extent)
                    (Space.pair_measurable
                      (Space.second_measurable
                        (Space.product target (Space.pi fun _ : Fin extent => target)) target)
                      (MeasurableMap.comp
                        (Space.second_measurable target (Space.pi fun _ : Fin extent => target))
                        (Space.first_measurable
                          (Space.product target (Space.pi fun _ : Fin extent => target)) target)))))
              have joint := Kernel.lintegral_measurable_joint
                (Kernel.const (Space.product target (Space.pi fun _ : Fin extent => target))
                  (family 0 input))
                (IsSFinite.const _ ((finite 0).measure input))
                (function := fun (value : β × (Fin extent → β)) (first : β) =>
                  function (value.1, fun position => Fin.cases first value.2 position))
                jointMeasurable
              exact joint
          rw [finProduct_succ_apply (extent + 1) family finite input,
            lintegral_map _ _ (cons_measurable target (extent + 1)) splitMeasurable,
            lintegral_prod_symm _ _ ((finite 0).measure input) _
              (ENNRealMeasurable.comp splitMeasurable (cons_measurable target (extent + 1)))]
          refine (lintegral_congr _ fun table => lintegral_congr _ fun first =>
              congrArg (fun rest => function (table lane, rest)) (laneSkip_succ_cons lane first table)).trans
            ((smaller (fun position => family position.succ) (fun position => finite position.succ) lane
              headMeasurable).trans ?_)
          apply lintegral_congr
          intro value
          have sectionMeasurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target)
              (fun rest => function (value, rest)) := by
            measurability
          rw [finProduct_succ_apply extent (fun position => family (laneSkip lane.succ position))
              (fun position => finite (laneSkip lane.succ position)) input,
            lintegral_map _ _ (cons_measurable target extent) sectionMeasurable,
            lintegral_prod_symm _ _ ((finite (laneSkip lane.succ 0)).measure input) _
              (ENNRealMeasurable.comp sectionMeasurable (cons_measurable target extent)),
            finProduct_congr_at extent (fun position => family (laneSkip lane.succ position.succ)) _
              (fun position => family (laneSkip lane position).succ)
              (fun position => finite (laneSkip lane position).succ) input input
              fun position => by rw [laneSkip_succ_succ]]
          apply lintegral_congr
          intro rest
          rw [laneSkip_succ_zero]

/-- The lane-split lemma: a finite product, read as one lane and the others in
order, is the product of that lane's measure and the product of the others. -/
theorem finProduct_split (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, IsSFinite (family lane)) (lane : Fin (extent + 1)) (input : α) :
    (finProduct (extent + 1) family finite input).map (laneSplit lane) (laneSplit_measurable lane) =
      Measure.prod (family lane input)
        (finProduct extent (fun position => family (laneSkip lane position))
          (fun position => finite (laneSkip lane position)) input)
        ((IsSFinite.finProduct extent _ fun position => finite (laneSkip lane position)).measure
          input) := by
  apply Measure.ext
  intro region measurable
  have indicatorMeasurable : ENNRealMeasurable
      (Space.product target (Space.pi fun _ : Fin extent => target))
      (ennrealIndicator region fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant _ ENNReal.one)
  rw [apply_eq_lintegral_indicator _ measurable, apply_eq_lintegral_indicator _ measurable,
    lintegral_map _ _ (laneSplit_measurable lane) indicatorMeasurable,
    lintegral_prod _ _ _ indicatorMeasurable]
  exact lintegral_finProduct_split extent family finite lane input indicatorMeasurable

/-! ### Inserting a lane -/

/-- The position among the other lanes of a lane other than `lane`. -/
@[expose] def laneOther {extent : Nat} (lane position : Fin (extent + 1)) : Option (Fin extent) :=
  if lower : position.val < lane.val then
    some ⟨position.val, by have := lane.isLt; omega⟩
  else if above : lane.val < position.val then
    some ⟨position.val - 1, by have := position.isLt; omega⟩
  else none

/-- Put `pair.1` at `lane` and the lanes of `pair.2` around it, in order. It
inverts `laneSplit` (`laneInsert_split`). -/
@[expose] def laneInsert {extent : Nat} (lane : Fin (extent + 1))
    (pair : β × (Fin extent → β)) (position : Fin (extent + 1)) : β :=
  match laneOther lane position with
  | none => pair.1
  | some other => pair.2 other

theorem laneInsert_self {extent : Nat} (lane : Fin (extent + 1))
    (pair : β × (Fin extent → β)) : laneInsert lane pair lane = pair.1 := by
  unfold laneInsert laneOther
  simp

theorem laneInsert_split {extent : Nat} (lane : Fin (extent + 1))
    (table : Fin (extent + 1) → β) : laneInsert lane (laneSplit lane table) = table := by
  funext position
  unfold laneInsert laneOther laneSplit
  by_cases lower : position.val < lane.val
  · simp only [lower, ↓reduceDIte]
    apply congrArg table
    apply Fin.ext
    unfold laneSkip
    simp [lower]
  · by_cases above : lane.val < position.val
    · simp only [lower, above, ↓reduceDIte]
      apply congrArg table
      apply Fin.ext
      unfold laneSkip
      have notBelow : ¬position.val - 1 < lane.val := by omega
      simp only [notBelow, ↓reduceIte]
      omega
    · simp only [lower, above, ↓reduceDIte]
      exact congrArg table (Fin.ext (by omega))

theorem laneInsert_measurable {extent : Nat}
    (lane : Fin (extent + 1)) :
    MeasurableMap (Space.product target (Space.pi fun _ : Fin extent => target))
      (Space.pi fun _ : Fin (extent + 1) => target) (laneInsert lane) := by
  refine Space.pi_measurable (spaces := fun _ : Fin (extent + 1) => target) fun position => ?_
  cases other : laneOther lane position with
  | none =>
      simp only [laneInsert, other]
      exact Space.first_measurable _ _
  | some index =>
      simp only [laneInsert, other]
      exact MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin extent => target) index)
        (Space.second_measurable _ _)

/-! ### Products with one lane pinned -/

/-- The family `family` with lane `lane` replaced by `pinned`. -/
@[expose] noncomputable def pinLane {extent : Nat} (family : Fin extent → Kernel source target)
    (lane : Fin extent) (pinned : Kernel source target) : Fin extent → Kernel source target :=
  fun position => if position = lane then pinned else family position

noncomputable def pinLaneFinite {extent : Nat} {family : Fin extent → Kernel source target}
    (finite : ∀ position, Kernel.IsSFinite (family position)) (lane : Fin extent)
    {pinned : Kernel source target} (pinnedFinite : Kernel.IsSFinite pinned) :
    ∀ position, Kernel.IsSFinite (pinLane family lane pinned position) := fun position =>
  if same : position = lane then by
    unfold pinLane
    rw [ite_eq_left same]
    exact pinnedFinite
  else by
    unfold pinLane
    rw [ite_eq_right same]
    exact finite position

/-- Integrating against a finite product reads one lane, and the other lanes
around it. -/
theorem lintegral_finProduct_insert (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, Kernel.IsSFinite (family lane)) (lane : Fin (extent + 1)) (input : α)
    {function : (Fin (extent + 1) → β) → ENNReal}
    (measurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target) function) :
    lintegral (Kernel.finProduct (extent + 1) family finite input) function =
      lintegral (family lane input) fun value =>
        lintegral (Kernel.finProduct extent (fun position => family (laneSkip lane position))
          (fun position => finite (laneSkip lane position)) input)
          fun rest => function (laneInsert lane (value, rest)) := by
  have split := lintegral_finProduct_split extent family finite lane input
    (function := fun pair => function (laneInsert lane pair))
    (measurable.comp (laneInsert_measurable lane))
  simp only [laneInsert_split] at split
  exact split

/-- A product whose lane `lane` is pinned to `value` integrates the other lanes
with `value` inserted at `lane`. -/
theorem lintegral_finProduct_pinned (extent : Nat) (family : Fin (extent + 1) → Kernel source target)
    (finite : ∀ lane, Kernel.IsSFinite (family lane)) (lane : Fin (extent + 1))
    (pinned : Kernel source target) (pinnedFinite : Kernel.IsSFinite pinned) (input : α)
    (value : β) (pinnedAt : pinned input = Measure.dirac target value)
    {function : (Fin (extent + 1) → β) → ENNReal}
    (measurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target) function) :
    lintegral (Kernel.finProduct (extent + 1) (pinLane family lane pinned)
        (pinLaneFinite finite lane pinnedFinite) input) function =
      lintegral (Kernel.finProduct extent (fun position => family (laneSkip lane position))
          (fun position => finite (laneSkip lane position)) input)
        fun rest => function (laneInsert lane (value, rest)) := by
  rw [lintegral_finProduct_insert extent _ _ lane input measurable]
  have atLane : pinLane family lane pinned lane input = Measure.dirac target value := by
    unfold pinLane
    rw [ite_eq_left rfl]
    exact pinnedAt
  have others : Kernel.finProduct extent
      (fun position => pinLane family lane pinned (laneSkip lane position))
      (fun position => pinLaneFinite finite lane pinnedFinite (laneSkip lane position))
      input =
      Kernel.finProduct extent (fun position => family (laneSkip lane position))
        (fun position => finite (laneSkip lane position)) input :=
    finProduct_congr_at extent _ _ _ _ input input fun position => by
      unfold pinLane
      rw [ite_eq_right (laneSkip_ne lane position)]
  have restFinite := (Kernel.IsSFinite.finProduct extent
    (fun position => family (laneSkip lane position))
    (fun position => finite (laneSkip lane position))).measure input
  rw [atLane, others]
  exact lintegral_dirac _ _ (Kernel.lintegral_measurable_joint
    (Kernel.const target _) (Kernel.IsSFinite.const target restFinite)
    (function := fun value rest => function (laneInsert lane (value, rest)))
    (measurable.comp (laneInsert_measurable lane)))

/-! ### Lane marginals -/

section Marginals

private theorem lintegral_const_of_probability (measure : Measure target)
    (probability : Measure.IsProbability measure) (value : ENNReal) :
    lintegral measure (fun _ => value) = value := by
  rw [lintegral_const, probability.univ_eq_one, ENNReal.mul_one]

/-- Fixing the first argument of a measurable function of two values leaves a
measurable function of the second. -/
private theorem pair_section_measurable {function : β × β → ENNReal}
    (functionMeasurable : ENNRealMeasurable (Space.product target target) function) (value : β) :
    ENNRealMeasurable target (fun other => function (value, other)) := by
  measurability

/-- Two iterated integrals against s-finite measures may be taken in either order. -/
private theorem lintegral_exchange (outer inner : Measure target)
    (outerFinite : Measure.SFinite outer) (innerFinite : Measure.SFinite inner)
    {function : β × β → ENNReal}
    (functionMeasurable : ENNRealMeasurable (Space.product target target) function) :
    lintegral outer (fun value => lintegral inner (fun other => function (value, other))) =
      lintegral inner (fun other => lintegral outer (fun value => function (value, other))) :=
  (lintegral_prod outer inner innerFinite functionMeasurable).symm.trans
    (lintegral_prod_symm outer inner outerFinite innerFinite functionMeasurable)

/-- Reading one lane of a product of probability kernels reads that lane's
kernel. The other lanes integrate a constant, which a probability returns. -/
theorem lintegral_finProduct_coordinate :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
    (finite : ∀ lane, IsSFinite (family lane)) →
    (∀ lane input, Measure.IsProbability (family lane input)) →
    (lane : Fin extent) → (input : α) → (function : β → ENNReal) →
    ENNRealMeasurable target function →
    lintegral (finProduct extent family finite input) (fun table => function (table lane)) =
      lintegral (family lane input) function
  | 0, _, _, _, lane, _, _, _ => lane.elim0
  | extent + 1, family, finite, markov, lane, input, function, functionMeasurable => by
    have laneMeasurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target)
        (fun table => function (table lane)) :=
      ENNRealMeasurable.comp functionMeasurable
        (Space.coordinate_measurable (fun _ : Fin (extent + 1) => target) lane)
    rw [finProduct_succ_apply, lintegral_map _ _ (cons_measurable target extent) laneMeasurable]
    have productMeasurable :
        ENNRealMeasurable (Space.product target (Space.pi fun _ : Fin extent => target))
          (fun pair => function (Fin.cases pair.1 pair.2 lane)) := by
      have composite := ENNRealMeasurable.comp laneMeasurable (cons_measurable target extent)
      exact composite
    induction lane using Fin.cases with
    | zero =>
        rw [lintegral_prod _ _ _ productMeasurable]
        apply lintegral_congr
        intro value
        exact lintegral_const_of_probability _
          (finProduct_markov extent _ _ (fun lane => markov lane.succ) input) (function value)
    | succ position =>
        rw [lintegral_prod_symm _ _ ((finite 0).measure input) _ productMeasurable]
        rw [← lintegral_finProduct_coordinate extent (fun lane => family lane.succ)
          (fun lane => finite lane.succ) (fun lane => markov lane.succ) position input function
          functionMeasurable]
        apply lintegral_congr
        intro table
        exact lintegral_const_of_probability _ (markov 0 input) (function (table position))

/-- Reading two distinct lanes of a product of probability kernels reads their
two kernels independently. The head factor supplies one of the two lanes and
the tail reads the other, or it supplies neither and integrates away. -/
theorem lintegral_finProduct_pair :
    (extent : Nat) → (family : Fin extent → Kernel source target) →
    (finite : ∀ lane, IsSFinite (family lane)) →
    (∀ lane input, Measure.IsProbability (family lane input)) →
    (first second : Fin extent) → first ≠ second → (input : α) →
    (function : β × β → ENNReal) → ENNRealMeasurable (Space.product target target) function →
    lintegral (finProduct extent family finite input)
        (fun table => function (table first, table second)) =
      lintegral (family first input) (fun value =>
        lintegral (family second input) (fun other => function (value, other)))
  | 0, _, _, _, first, _, _, _, _, _ => first.elim0
  | extent + 1, family, finite, markov, first, second, distinct, input, function,
      functionMeasurable => by
    have pairMeasurable : ENNRealMeasurable (Space.pi fun _ : Fin (extent + 1) => target)
        (fun table => function (table first, table second)) := by
      measurability
    rw [finProduct_succ_apply, lintegral_map _ _ (cons_measurable target extent) pairMeasurable]
    have productMeasurable :
        ENNRealMeasurable (Space.product target (Space.pi fun _ : Fin extent => target))
          (fun pair => function
            (Fin.cases pair.1 pair.2 first, Fin.cases pair.1 pair.2 second)) := by
      have composite := ENNRealMeasurable.comp pairMeasurable (cons_measurable target extent)
      exact composite
    induction first using Fin.cases with
    | zero =>
        induction second using Fin.cases with
        | zero => exact absurd rfl distinct
        | succ second =>
            rw [lintegral_prod _ _ _ productMeasurable]
            apply lintegral_congr
            intro value
            exact lintegral_finProduct_coordinate extent (fun lane => family lane.succ)
              (fun lane => finite lane.succ) (fun lane => markov lane.succ) second input
              (fun other => function (value, other))
              (pair_section_measurable functionMeasurable value)
    | succ first =>
        induction second using Fin.cases with
        | zero =>
            rw [lintegral_prod _ _ _ productMeasurable]
            have swappedMeasurable : ENNRealMeasurable (Space.product target target)
                (fun pair => function (pair.2, pair.1)) :=
              ENNRealMeasurable.comp functionMeasurable (Space.swap_measurable target target)
            refine (lintegral_congr _ fun value => ?_).trans
              (lintegral_exchange (family 0 input) (family first.succ input)
                ((finite 0).measure input) ((finite first.succ).measure input)
                swappedMeasurable)
            exact lintegral_finProduct_coordinate extent (fun lane => family lane.succ)
              (fun lane => finite lane.succ) (fun lane => markov lane.succ) first input
              (fun other => function (other, value))
              (pair_section_measurable swappedMeasurable value)
        | succ second =>
            rw [lintegral_prod_symm _ _ ((finite 0).measure input) _ productMeasurable]
            rw [← lintegral_finProduct_pair extent (fun lane => family lane.succ)
              (fun lane => finite lane.succ) (fun lane => markov lane.succ) first second
              (fun equal => distinct (congrArg Fin.succ equal)) input function
              functionMeasurable]
            apply lintegral_congr
            intro table
            exact lintegral_const_of_probability _ (markov 0 input)
              (function (table first, table second))

end Marginals

end

end Kernel

end Problib.Measure
