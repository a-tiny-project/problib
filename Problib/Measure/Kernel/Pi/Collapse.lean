module

public import Problib.Measure.Kernel.Pi.Law
public import Problib.Measure.Kernel.Composition.Bind.Core
public import Problib.Measure.Integral.Density.Basic
public import Problib.Measure.Additive.Dirac
import Problib.Measure.Kernel.Pi.Reads
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Extended.Algebra.Binary

set_option autoImplicit false

/-!
# Eliminating scored entries of a product law

Items read a product law at the keys an assignment gives them, and each item
scores the value it reads. Weighting the product by the items' scores and
reading the items' keys gives, at each key the items use, the key's law
weighted by the product of the scores of the items there. When that weighted
law is a finite mass `Z` times a probability law `R`, the whole weighted read
is the product of the masses of the used keys times the read of a product of
the `R`s (`collapse`). A key no item reads integrates to one and needs no
factorization, so its posterior law is arbitrary.

At an allocation of assignments, a kernel that is a scaled probability law at
every assignment binds as the allocation reweighted by the scales, bound to the
probability laws (`bind_scaled`). When those laws return their assignment, the
assignment marginal is the reweighted allocation (`map_bind_scaled`). Together
with `collapse` at each assignment, the assignment marginal of a scored memo
block is the allocation with density the product of the used keys' masses, and
the block is that marginal followed by independent posterior draws.

The proof integrates a product of functions of distinct coordinates one key at
a time (`IsProduct.lintegral_massProduct`, from `IsProduct.lintegral_read`),
after grouping the items by key (`massProduct_group`). Both sides of
`collapse` then agree on cylinders, which determine finite measures.
-/

namespace Problib.Measure.Pi

open Problib.Real

universe u v w

public section

variable {ι : Type u} {α : Type v} {space : Space α}

/-! ### Products of masses -/

theorem massProduct_mul (keys : List ι) (left right : ι → ENNReal) :
    massProduct keys (fun key => ENNReal.mul (left key) (right key)) =
      ENNReal.mul (massProduct keys left) (massProduct keys right) := by
  induction keys with
  | nil => exact (ENNReal.one_mul _).symm
  | cons key rest induction =>
      rw [massProduct_cons, massProduct_cons, massProduct_cons, induction]
      calc ENNReal.mul (ENNReal.mul (left key) (right key))
            (ENNReal.mul (massProduct rest left) (massProduct rest right))
          = ENNReal.mul (left key) (ENNReal.mul (ENNReal.mul (right key) (massProduct rest left))
              (massProduct rest right)) := by
            rw [ENNReal.mul_assoc, ENNReal.mul_assoc (right key)]
        _ = ENNReal.mul (left key) (ENNReal.mul (ENNReal.mul (massProduct rest left) (right key))
              (massProduct rest right)) := by
            rw [ENNReal.mul_comm (right key)]
        _ = ENNReal.mul (ENNReal.mul (left key) (massProduct rest left))
              (ENNReal.mul (right key) (massProduct rest right)) := by
            rw [ENNReal.mul_assoc (massProduct rest left), ENNReal.mul_assoc]

theorem massProduct_one (keys : List ι) : massProduct keys (fun _ => ENNReal.one) = ENNReal.one := by
  induction keys with
  | nil => rfl
  | cons key rest induction => rw [massProduct_cons, induction, ENNReal.one_mul]

theorem massProduct_measurable {β : Type w} {source : Space β} (keys : List ι)
    {functions : ι → β → ENNReal} (measurable : ∀ key ∈ keys, ENNRealMeasurable source (functions key)) :
    ENNRealMeasurable source fun point => massProduct keys fun key => functions key point := by
  induction keys with
  | nil => exact ENNRealMeasurable.constant source ENNReal.one
  | cons key rest induction =>
      exact ENNRealMeasurable.mul (measurable key (List.Mem.head _))
        (induction fun other member => measurable other (List.Mem.tail _ member))

/-- A product of indicators is the indicator of the cylinder they cut out. -/
theorem massProduct_indicator (keys : List ι) (sets : ι → Set α) (functions : ι → α → ENNReal)
    (point : ι → α) :
    massProduct keys (fun key => ennrealIndicator (sets key) (functions key) (point key)) =
      ennrealIndicator (cylinder keys sets)
        (fun point => massProduct keys fun key => functions key (point key)) point := by
  induction keys with
  | nil =>
      rw [ennrealIndicator_of_mem (show cylinder [] sets point from fun _ member => nomatch member)]
      rfl
  | cons key rest induction =>
      have split : cylinder (key :: rest) sets point ↔
          sets key (point key) ∧ cylinder rest sets point :=
        ⟨fun inside => ⟨inside key (List.Mem.head _), fun other member =>
            inside other (List.Mem.tail _ member)⟩,
          fun inside other member => by
            cases member with
            | head => exact inside.1
            | tail _ member => exact inside.2 other member⟩
      rw [massProduct_cons, induction]
      by_cases atKey : sets key (point key)
      · rw [ennrealIndicator_of_mem atKey]
        by_cases rest : cylinder rest sets point
        · rw [ennrealIndicator_of_mem rest, ennrealIndicator_of_mem (split.mpr ⟨atKey, rest⟩)]
          rfl
        · rw [ennrealIndicator_of_not_mem rest, ennrealIndicator_of_not_mem
            fun inside => rest (split.mp inside).2, ENNReal.mul_zero]
      · rw [ennrealIndicator_of_not_mem atKey, ennrealIndicator_of_not_mem
          fun inside => atKey (split.mp inside).1, ENNReal.zero_mul]

variable [DecidableEq ι]

/-- A product over items of a function of each item's key regroups as a
product over the distinct keys, each key contributing its own items. -/
theorem massProduct_group {β : Type w} (items : List β) (keys : β → ι)
    (functions : β → ι → ENNReal) :
    massProduct items (fun item => functions item (keys item)) =
      massProduct (distinct (items.map keys)) fun key =>
        massProduct items fun item => if keys item = key then functions item key else ENNReal.one := by
  induction items with
  | nil => rfl
  | cons item rest induction =>
      let others : ι → ENNReal := fun key =>
        massProduct rest fun other => if keys other = key then functions other key else ENNReal.one
      have mine : ∀ key, keys item ≠ key →
          (massProduct (item :: rest) fun other =>
            if keys other = key then functions other key else ENNReal.one) = others key :=
        fun key different => by rw [massProduct_cons, ite_eq_right different, ENNReal.one_mul]
      rw [massProduct_cons, induction]
      by_cases repeated : keys item ∈ rest.map keys
      · have collapsed : distinct ((item :: rest).map keys) = distinct (rest.map keys) := by
          simp only [List.map_cons, distinct, ite_eq_left repeated]
        obtain ⟨before, after, equal⟩ := List.append_of_mem (mem_distinct.mpr repeated)
        have fresh : keys item ∉ before ++ after := by
          have nodup := nodup_distinct (rest.map keys)
          rw [equal] at nodup
          intro member
          rcases List.mem_append.mp member with inBefore | inAfter
          · exact (List.nodup_append.mp nodup).2.2 _ inBefore _ (List.Mem.head _) rfl
          · exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 inAfter
        rw [collapsed, equal, massProduct_middle, massProduct_middle, massProduct_cons, ite_eq_left rfl,
          massProduct_congr (keys := before ++ after) fun key member =>
            mine key fun same => fresh (by rw [same]; exact member), ENNReal.mul_assoc]
      · have spread : distinct ((item :: rest).map keys) = keys item :: distinct (rest.map keys) := by
          simp only [List.map_cons, distinct, ite_eq_right repeated]
        have alone : others (keys item) = ENNReal.one :=
          (massProduct_congr fun other member => ite_eq_right fun same =>
            repeated (by rw [← same]; exact List.mem_map_of_mem member)).trans (massProduct_one rest)
        rw [spread, massProduct_cons, massProduct_cons, ite_eq_left rfl,
          massProduct_congr (keys := distinct (rest.map keys)) fun key member =>
            mine key fun same => repeated (by rw [same]; exact mem_distinct.mp member)]
        change _ = ENNReal.mul (ENNReal.mul _ (others (keys item))) _
        rw [alone, ENNReal.mul_one]

/-- The product of the scores of the items an assignment sends to one key. -/
@[expose] noncomputable def localScore {n : Nat} (keys : Fin n → ι) (score : Fin n → α → ENNReal)
    (key : ι) (value : α) : ENNReal :=
  massProduct (List.finRange n) fun item => if keys item = key then score item value else ENNReal.one

end

namespace IsProduct

public section

variable {ι : Type u} {α : Type v} {space : Space α}
  {measure : Measure (Space.pi fun _ : ι => space)} {laws : ι → Measure space}

/-- Under a product law, a product of functions of distinct coordinates
integrates to the product of their integrals. -/
theorem lintegral_massProduct (product : IsProduct measure laws) {keys : List ι}
    (distinctKeys : keys.Nodup) {functions : ι → α → ENNReal}
    (measurable : ∀ key ∈ keys, ENNRealMeasurable space (functions key)) :
    lintegral measure (fun point => massProduct keys fun key => functions key (point key)) =
      massProduct keys fun key => lintegral (laws key) (functions key) := by
  induction keys with
  | nil =>
      change lintegral measure (fun _ => ENNReal.one) = ENNReal.one
      rw [lintegral_const, product.probability.univ_eq_one, ENNReal.one_mul]
  | cons key rest induction =>
      have split := List.nodup_cons.mp distinctKeys
      have restMeasurable : ∀ other ∈ rest, ENNRealMeasurable space (functions other) :=
        fun other member => measurable other (List.Mem.tail _ member)
      have restCoordinates : ENNRealMeasurable (Space.pi fun _ : ι => space)
          fun point => massProduct rest fun other => functions other (point other) :=
        massProduct_measurable rest fun other member =>
          (restMeasurable other member).comp (Space.coordinate_measurable (fun _ : ι => space) other)
      have read := IsProduct.lintegral_read product key
        (Measure.SigmaFinite.ofFinite product.probability.to_finite).toSFinite
        (Measure.SigmaFinite.ofFinite (product.law_probability key).to_finite).toSFinite
        (function := fun pair =>
          ENNReal.mul (functions key pair.1) (massProduct rest fun other => functions other (pair.2 other)))
        (ENNRealMeasurable.mul ((measurable key (List.Mem.head _)).comp (Space.first_measurable _ _))
          (restCoordinates.comp (Space.second_measurable _ _)))
        (fun value point => congrArg (ENNReal.mul (functions key value)) (massProduct_congr
          fun other member => by
            change functions other (replace point key value other) = functions other (point other)
            rw [replace_other _ _ fun same : other = key => split.1 (by rw [← same]; exact member)]))
      refine read.trans ?_
      calc lintegral (laws key) (fun value => lintegral measure fun point =>
            ENNReal.mul (functions key value) (massProduct rest fun other => functions other (point other)))
          = lintegral (laws key) (fun value => ENNReal.mul (massProduct rest fun other =>
              lintegral (laws other) (functions other)) (functions key value)) := by
            apply lintegral_congr
            intro value
            rw [lintegral_smul _ _ restCoordinates, induction split.2 restMeasurable, ENNReal.mul_comm]
        _ = _ := by
            rw [lintegral_smul _ _ (measurable key (List.Mem.head _)), ENNReal.mul_comm]
            rfl

variable [DecidableEq ι]

/-- Under a product law, a product of functions of the values items read at
their keys integrates key by key: each distinct key contributes the integral of
the product of its own items' functions. -/
theorem lintegral_reads (product : IsProduct measure laws) {n : Nat} (keys : Fin n → ι)
    {functions : Fin n → α → ENNReal} (measurable : ∀ item, ENNRealMeasurable space (functions item)) :
    lintegral measure (fun point => massProduct (List.finRange n) fun item =>
        functions item (point (keys item))) =
      massProduct (distinct ((List.finRange n).map keys)) fun key =>
        lintegral (laws key) fun value => massProduct (List.finRange n) fun item =>
          if keys item = key then functions item value else ENNReal.one := by
  rw [lintegral_congr measure fun point => massProduct_group (List.finRange n) keys
    fun item key => functions item (point key)]
  refine lintegral_massProduct product (nodup_distinct _) (functions := fun key value =>
    massProduct (List.finRange n) fun item =>
      if keys item = key then functions item value else ENNReal.one) fun key _ =>
    massProduct_measurable _ fun item _ => ?_
  by_cases same : keys item = key
  · simp only [same, ite_true]
    exact measurable item
  · simp only [same, ite_false]
    exact ENNRealMeasurable.constant space ENNReal.one

/-- Weighting a product law by the items' scores and reading the items' keys
is the product of the used keys' masses times the read of the posterior
product. Each used key's law, weighted by its items' scores, is its mass times
its posterior law. Keys no item reads need no factorization. -/
theorem collapse (product : IsProduct measure laws) {n : Nat} (keys : Fin n → ι)
    {score : Fin n → α → ENNReal} (scoreMeasurable : ∀ item, ENNRealMeasurable space (score item))
    {mass : ι → NNReal} {posteriors : ι → Measure space}
    (factor : ∀ item, (laws (keys item)).withDensity (localScore keys score (keys item)) =
      Measure.smul (ENNReal.finite (mass (keys item))) (posteriors (keys item)))
    {table : Measure (Space.pi fun _ : ι => space)} (tableProduct : IsProduct table posteriors) :
    (measure.withDensity fun point => massProduct (List.finRange n) fun item =>
        score item (point (keys item))).map (fun point item => point (keys item))
        (Space.pi_reindex (fun _ : ι => space) keys) =
      Measure.smul (massProduct (distinct ((List.finRange n).map keys)) fun key =>
          ENNReal.finite (mass key))
        (table.map (fun point item => point (keys item)) (Space.pi_reindex (fun _ : ι => space) keys)) := by
  have readMeasurable : MeasurableMap (Space.pi fun _ : ι => space) (Space.pi fun _ : Fin n => space)
      (fun point item => point (keys item)) :=
    Space.pi_reindex (fun _ : ι => space) keys
  let read : (ι → α) → Fin n → α := fun point item => point (keys item)
  let total := massProduct (distinct ((List.finRange n).map keys)) fun key => ENNReal.finite (mass key)
  -- One used key: its items' tests against its scored law are its mass times
  -- the tests against its posterior.
  have atKey : ∀ key ∈ distinct ((List.finRange n).map keys), ∀ tests : Fin n → α → ENNReal,
      (∀ item, ENNRealMeasurable space (tests item)) →
      lintegral (laws key) (fun value => massProduct (List.finRange n) fun item =>
          if keys item = key then ENNReal.mul (tests item value) (score item value) else ENNReal.one) =
        ENNReal.mul (ENNReal.finite (mass key)) (lintegral (posteriors key) fun value =>
          massProduct (List.finRange n) fun item => if keys item = key then tests item value else ENNReal.one) := by
    intro key used tests testsMeasurable
    obtain ⟨item, -, reads⟩ := List.mem_map.mp (mem_distinct.mp used)
    have each : ∀ (holds : Prop) [Decidable holds] (first second : ENNReal),
        (if holds then ENNReal.mul first second else ENNReal.one) =
          ENNReal.mul (if holds then first else ENNReal.one) (if holds then second else ENNReal.one) := by
      intro holds _ first second
      by_cases inside : holds
      · simp only [inside, ite_true]
      · simp only [inside, ite_false, ENNReal.one_mul]
    have testMeasurable := massProduct_measurable (List.finRange n) (functions := fun item value =>
        if keys item = key then tests item value else ENNReal.one) fun other _ => by
      by_cases same : keys other = key
      · simp only [same, ite_true]
        exact testsMeasurable other
      · simp only [same, ite_false]
        exact ENNRealMeasurable.constant space ENNReal.one
    have scoreProductMeasurable := massProduct_measurable (List.finRange n) (functions := fun item value =>
        if keys item = key then score item value else ENNReal.one) fun other _ => by
      by_cases same : keys other = key
      · simp only [same, ite_true]
        exact scoreMeasurable other
      · simp only [same, ite_false]
        exact ENNRealMeasurable.constant space ENNReal.one
    calc lintegral (laws key) (fun value => massProduct (List.finRange n) fun item =>
            if keys item = key then ENNReal.mul (tests item value) (score item value) else ENNReal.one)
        = lintegral (laws key) (fun value => ENNReal.mul (localScore keys score key value)
            (massProduct (List.finRange n) fun item =>
              if keys item = key then tests item value else ENNReal.one)) := by
          apply lintegral_congr
          intro value
          rw [massProduct_congr fun item _ => each _ _ _, massProduct_mul, ENNReal.mul_comm]
          rfl
      _ = lintegral ((laws key).withDensity (localScore keys score key)) (fun value =>
            massProduct (List.finRange n) fun item =>
              if keys item = key then tests item value else ENNReal.one) :=
          (lintegral_withDensity _ scoreProductMeasurable testMeasurable).symm
      _ = _ := by
          rw [← reads, factor item, lintegral_smul_measure]
  -- Agreement on the cylinders over items.
  have agree : ∀ set, cylinders (Fin n) space set →
      (measure.withDensity fun point => massProduct (List.finRange n) fun item =>
          score item (point (keys item))).map read readMeasurable set =
        Measure.smul total (table.map read readMeasurable) set := by
    rintro _ ⟨positions, sets, setsMeasurable, rfl⟩
    let whole : Fin n → Set α := fun item value => item ∈ positions → sets item value
    have wholeMeasurable : ∀ item, space.Measurable (whole item) := by
      intro item
      by_cases member : item ∈ positions
      · have equal : whole item = sets item :=
          funext fun value => propext ⟨fun implied => implied member, fun inside _ => inside⟩
        rw [equal]
        exact setsMeasurable item member
      · have equal : whole item = Set.univ :=
          funext fun value => propext ⟨fun _ => True.intro, fun _ held => absurd held member⟩
        rw [equal]
        exact space.univ
    have sameCylinder : cylinder positions sets = cylinder (List.finRange n) whole :=
      Set.ext fun point => ⟨fun inside item _ member => inside item member,
        fun inside item member => inside item (List.mem_finRange item) member⟩
    let tests : Fin n → α → ENNReal := fun item => ennrealIndicator (whole item) fun _ => ENNReal.one
    have testsMeasurable : ∀ item, ENNRealMeasurable space (tests item) := fun item =>
      ENNRealMeasurable.indicator (wholeMeasurable item) (ENNRealMeasurable.constant space ENNReal.one)
    have cylinderMeasurable := cylinder_measurable (space := space) (keys := positions) setsMeasurable
    have preimageMeasurable := readMeasurable cylinderMeasurable
    -- The read cylinder's indicator against a product of item functions.
    have indicate : ∀ (functions : Fin n → α → ENNReal) (point : ι → α),
        ennrealIndicator (Set.preimage read (cylinder positions sets))
            (fun point => massProduct (List.finRange n) fun item => functions item (point (keys item)))
            point =
          massProduct (List.finRange n) fun item =>
            ENNReal.mul (tests item (point (keys item))) (functions item (point (keys item))) := by
      intro functions point
      change ennrealIndicator (cylinder positions sets)
          (fun read => massProduct (List.finRange n) fun item => functions item (read item))
          (read point) = _
      rw [sameCylinder, ← massProduct_indicator]
      refine massProduct_congr fun item _ => ?_
      by_cases inside : whole item (point (keys item))
      · rw [ennrealIndicator_of_mem inside, show tests item (point (keys item)) = ENNReal.one from
          ennrealIndicator_of_mem inside, ENNReal.one_mul]
      · rw [ennrealIndicator_of_not_mem inside, show tests item (point (keys item)) = ENNReal.zero from
          ennrealIndicator_of_not_mem inside, ENNReal.zero_mul]
    have posteriorSide : table (Set.preimage read (cylinder positions sets)) =
        massProduct (distinct ((List.finRange n).map keys)) fun key =>
          lintegral (posteriors key) fun value => massProduct (List.finRange n) fun item =>
            if keys item = key then tests item value else ENNReal.one := by
      calc table (Set.preimage read (cylinder positions sets))
          = lintegral table (ennrealIndicator (Set.preimage read (cylinder positions sets))
              fun point => massProduct (List.finRange n) fun _ => ENNReal.one) := by
            rw [lintegral_indicator _ _ preimageMeasurable]
            simp only [massProduct_one]
            rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.one_mul]
        _ = lintegral table (fun point => massProduct (List.finRange n) fun item =>
              tests item (point (keys item))) := by
            apply lintegral_congr
            intro point
            rw [indicate (fun _ _ => ENNReal.one)]
            exact massProduct_congr fun item _ => ENNReal.mul_one _
        _ = _ := tableProduct.lintegral_reads keys testsMeasurable
    rw [Measure.map_apply _ _ _ cylinderMeasurable, Measure.smul_apply_measurable _ _ cylinderMeasurable,
      Measure.map_apply _ _ _ cylinderMeasurable, posteriorSide, Measure.withDensity_apply _ _ preimageMeasurable,
      ← lintegral_indicator _ _ preimageMeasurable, lintegral_congr measure (indicate score),
      product.lintegral_reads keys (functions := fun item value => ENNReal.mul (tests item value) (score item value))
        fun item => ENNRealMeasurable.mul (testsMeasurable item) (scoreMeasurable item),
      massProduct_congr fun key used => atKey key used tests testsMeasurable, massProduct_mul]
  have rightFinite : Measure.IsFinite (Measure.smul total (table.map read readMeasurable)) :=
    Measure.IsFinite.smul total (massProduct_finite fun _ _ => True.intro)
      (Measure.IsFinite.map tableProduct.probability.to_finite read readMeasurable)
  have leftFinite : Measure.IsFinite ((measure.withDensity fun point =>
      massProduct (List.finRange n) fun item => score item (point (keys item))).map read readMeasurable) :=
    ⟨by rw [agree Set.univ cylinders_univ]; exact rightFinite.univ_finite⟩
  exact Measure.ext_of_generate (cylinders (Fin n) space) cylinders_generate cylinders_pi cylinders_univ
    leftFinite rightFinite agree

end

end IsProduct

end Problib.Measure.Pi

namespace Problib.Measure.Measure

open Problib.Real

universe u v

public section

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Binding an allocation against a kernel that is a scaled probability law at
every point binds the allocation reweighted by the scales against the laws. -/
theorem bind_scaled (allocation : Measure source) {scale : α → ENNReal}
    (scaleMeasurable : ENNRealMeasurable source scale) {scaled laws : Kernel source target}
    (pointwise : ∀ point, scaled point = Measure.smul (scale point) (laws point)) :
    allocation.bind scaled = (allocation.withDensity scale).bind laws := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply _ _ setMeasurable, bind_apply _ _ setMeasurable,
    lintegral_withDensity _ scaleMeasurable (laws.measurable setMeasurable)]
  apply lintegral_congr
  intro point
  rw [pointwise, Measure.smul_apply_measurable _ _ setMeasurable]

/-- When each law returns its own point through a view, the view of the bind
of an allocation against the scaled laws is the allocation reweighted by the
scales. -/
theorem map_bind_scaled (allocation : Measure source) {scale : α → ENNReal}
    {scaled laws : Kernel source target}
    (pointwise : ∀ point, scaled point = Measure.smul (scale point) (laws point))
    (view : β → α) (viewMeasurable : MeasurableMap target source view)
    (returns : ∀ point, (laws point).map view viewMeasurable = Measure.dirac source point) :
    (allocation.bind scaled).map view viewMeasurable = allocation.withDensity scale := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable, bind_apply _ _ (viewMeasurable setMeasurable),
    withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable]
  apply lintegral_congr
  intro point
  rw [pointwise, Measure.smul_apply_measurable _ _ (viewMeasurable setMeasurable),
    ← (laws point).map_apply view viewMeasurable setMeasurable, returns,
    Measure.dirac_apply _ _ setMeasurable]
  by_cases member : set point
  · rw [ite_eq_left member, ENNReal.mul_one, ennrealIndicator_of_mem member]
  · rw [ite_eq_right member, ENNReal.mul_zero, ennrealIndicator_of_not_mem member]

end

end Problib.Measure.Measure
