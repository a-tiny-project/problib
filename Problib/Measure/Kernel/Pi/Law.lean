module

public import Problib.Measure.Pi
public import Problib.Measure.Dynkin.Uniqueness
public import Problib.Measure.Kernel.Product.Uniqueness

set_option autoImplicit false

/-!
# Countable product laws

A measure on the product space `ι → α` is the product of a family of laws when
every finite cylinder over distinct keys has the product of its coordinate
masses. Such a measure has total mass one and is unique. The product shape
survives coordinatewise maps, reindexing along an injection, regrouping the
coordinates into blocks, and prepending one independent coordinate. Each
coordinate has its own law, and distinct coordinates are independent, so
redrawing one coordinate from its law and writing it over the old one leaves
the product where it was.

The shape is reached from any class of sets that determines finite measures on
the coordinate space: agreement on cylinders built from that class extends to
all measurable cylinders one key at a time.
-/

namespace Problib.Measure.Pi

open Problib.Real

universe u v w x

public section

variable {ι : Type u} {α : Type v} {space : Space α}

/-- Points whose listed keys lie in their sets. Keys may repeat. -/
@[expose] def cylinder (keys : List ι) (sets : ι → Set α) : Set (ι → α) :=
  fun point => ∀ key ∈ keys, sets key (point key)

/-- The product of one mass per listed key. -/
@[expose] noncomputable def massProduct (keys : List ι) (mass : ι → ENNReal) : ENNReal :=
  keys.foldr (fun key total => ENNReal.mul (mass key) total) ENNReal.one

theorem massProduct_nil (mass : ι → ENNReal) : massProduct [] mass = ENNReal.one := rfl

theorem massProduct_cons (key : ι) (keys : List ι) (mass : ι → ENNReal) :
    massProduct (key :: keys) mass = ENNReal.mul (mass key) (massProduct keys mass) := rfl

theorem massProduct_append (first second : List ι) (mass : ι → ENNReal) :
    massProduct (first ++ second) mass =
      ENNReal.mul (massProduct first mass) (massProduct second mass) := by
  induction first with
  | nil => exact (ENNReal.one_mul _).symm
  | cons key rest induction =>
      rw [List.cons_append, massProduct_cons, massProduct_cons, induction, ENNReal.mul_assoc]

theorem massProduct_map {κ : Type w} (function : κ → ι) (keys : List κ) (mass : ι → ENNReal) :
    massProduct (keys.map function) mass = massProduct keys fun key => mass (function key) := by
  induction keys with
  | nil => rfl
  | cons key rest induction => rw [List.map_cons, massProduct_cons, massProduct_cons, induction]

theorem massProduct_flatMap {κ : Type w} (keys : List κ) (family : κ → List ι)
    (mass : ι → ENNReal) :
    massProduct (keys.flatMap family) mass =
      massProduct keys fun key => massProduct (family key) mass := by
  induction keys with
  | nil => rfl
  | cons key rest induction =>
      rw [List.flatMap_cons, massProduct_append, induction, massProduct_cons]

theorem massProduct_congr {keys : List ι} {left right : ι → ENNReal}
    (same : ∀ key ∈ keys, left key = right key) :
    massProduct keys left = massProduct keys right := by
  induction keys with
  | nil => rfl
  | cons key rest induction =>
      rw [massProduct_cons, massProduct_cons, same key (List.Mem.head _),
        induction fun other member => same other (List.Mem.tail _ member)]

/-- Permuting the factors leaves their joint mass unchanged. -/
theorem massProduct_perm {first second : List ι} (permutation : first.Perm second)
    (mass : ι → ENNReal) : massProduct first mass = massProduct second mass := by
  apply permutation.foldr_eq'
  intro left _ right _ total
  rw [← ENNReal.mul_assoc, ENNReal.mul_comm (mass right) (mass left), ENNReal.mul_assoc]

theorem massProduct_finite {keys : List ι} {mass : ι → ENNReal}
    (finite : ∀ key ∈ keys, ENNReal.Finite (mass key)) :
    ENNReal.Finite (massProduct keys mass) := by
  induction keys with
  | nil => exact True.intro
  | cons key rest induction =>
      exact ENNReal.mul_finite (finite key (List.Mem.head _))
        (induction fun other member => finite other (List.Mem.tail _ member))

/-- A product over keys with one key in the middle is that key's mass times the
product over the others. -/
theorem massProduct_middle (before after : List ι) (key : ι) (mass : ι → ENNReal) :
    massProduct (before ++ key :: after) mass =
      ENNReal.mul (mass key) (massProduct (before ++ after) mass) := by
  rw [massProduct_append, massProduct_cons, massProduct_append]
  calc
    ENNReal.mul (massProduct before mass) (ENNReal.mul (mass key) (massProduct after mass)) =
        ENNReal.mul (ENNReal.mul (massProduct before mass) (mass key)) (massProduct after mass) :=
      (ENNReal.mul_assoc _ _ _).symm
    _ = ENNReal.mul (ENNReal.mul (mass key) (massProduct before mass)) (massProduct after mass) := by
      rw [ENNReal.mul_comm (massProduct before mass) (mass key)]
    _ = ENNReal.mul (mass key) (ENNReal.mul (massProduct before mass) (massProduct after mass)) :=
      ENNReal.mul_assoc _ _ _

/-- The keys of a list with repeats removed. -/
@[expose] noncomputable def distinct : List ι → List ι
  | [] => []
  | key :: rest =>
      @ite _ (key ∈ rest) (Classical.propDecidable _) (distinct rest) (key :: distinct rest)

theorem mem_distinct {key : ι} {keys : List ι} : key ∈ distinct keys ↔ key ∈ keys := by
  induction keys with
  | nil => exact Iff.rfl
  | cons head rest induction =>
      by_cases repeated : head ∈ rest
      · simp only [distinct, ite_eq_left repeated, induction, List.mem_cons]
        exact ⟨Or.inr, fun member => member.elim (fun same => same ▸ repeated) id⟩
      · simp only [distinct, ite_eq_right repeated, induction, List.mem_cons]

theorem nodup_distinct (keys : List ι) : (distinct keys).Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons head rest induction =>
      by_cases repeated : head ∈ rest
      · simp only [distinct, ite_eq_left repeated]
        exact induction
      · simp only [distinct, ite_eq_right repeated]
        exact List.nodup_cons.mpr ⟨fun member => repeated (mem_distinct.mp member), induction⟩

theorem cylinder_nil (sets : ι → Set α) : cylinder [] sets = Set.univ := by
  apply Set.ext
  intro point
  exact ⟨fun _ => True.intro, fun _ key member => (nomatch member)⟩

theorem cylinder_cons (key : ι) (keys : List ι) (sets : ι → Set α) :
    cylinder (key :: keys) sets =
      Set.inter (Set.preimage (fun point => point key) (sets key)) (cylinder keys sets) := by
  apply Set.ext
  intro point
  constructor
  · intro inside
    exact ⟨inside key (List.Mem.head _), fun other member => inside other (List.Mem.tail _ member)⟩
  · rintro ⟨first, rest⟩ other member
    cases member with
    | head => exact first
    | tail _ member => exact rest other member

theorem cylinder_single (key : ι) (set : Set α) :
    cylinder [key] (fun _ => set) = Set.preimage (fun point : ι → α => point key) set := by
  rw [cylinder_cons, cylinder_nil, Set.inter_univ_right]

theorem cylinder_congr {keys : List ι} {left right : ι → Set α}
    (same : ∀ key ∈ keys, left key = right key) : cylinder keys left = cylinder keys right := by
  apply Set.ext
  intro point
  constructor
  · intro inside key member
    rw [← same key member]
    exact inside key member
  · intro inside key member
    rw [same key member]
    exact inside key member

theorem cylinder_distinct (keys : List ι) (sets : ι → Set α) :
    cylinder (distinct keys) sets = cylinder keys sets := by
  apply Set.ext
  intro point
  exact ⟨fun inside key member => inside key (mem_distinct.mpr member),
    fun inside key member => inside key (mem_distinct.mp member)⟩

theorem cylinder_measurable {keys : List ι} {sets : ι → Set α}
    (measurable : ∀ key ∈ keys, space.Measurable (sets key)) :
    (Space.pi fun _ : ι => space).Measurable (cylinder keys sets) := by
  induction keys with
  | nil =>
      rw [cylinder_nil]
      exact (Space.pi fun _ : ι => space).univ
  | cons key rest induction =>
      rw [cylinder_cons]
      exact (Space.pi fun _ : ι => space).inter
        (Space.coordinate_measurable (fun _ : ι => space) key (measurable key (List.Mem.head _)))
        (induction fun other member => measurable other (List.Mem.tail _ member))

/-- `measure` is the product of `laws`: every cylinder over distinct keys and
measurable sets has the product of its coordinate masses. -/
@[expose] def IsProduct (measure : Measure (Space.pi fun _ : ι => space))
    (laws : ι → Measure space) : Prop :=
  ∀ keys : List ι, keys.Nodup → ∀ sets : ι → Set α,
    (∀ key ∈ keys, space.Measurable (sets key)) →
      measure (cylinder keys sets) = massProduct keys fun key => laws key (sets key)

/-- Finite cylinders over measurable sets. -/
@[expose] def cylinders (ι : Type u) (space : Space α) : Set (Set (ι → α)) :=
  fun set => ∃ keys : List ι, ∃ sets : ι → Set α,
    (∀ key ∈ keys, space.Measurable (sets key)) ∧ set = cylinder keys sets

theorem cylinders_pi : PiSystem (cylinders ι space) := by
  intro left right leftMember rightMember
  obtain ⟨leftKeys, leftSets, leftMeasurable, rfl⟩ := leftMember
  obtain ⟨rightKeys, rightSets, rightMeasurable, rfl⟩ := rightMember
  have piece : ∀ (holds : Prop) (set : Set α), (holds → space.Measurable set) →
      space.Measurable (fun value => holds → set value) := by
    intro holds set measurable
    by_cases inside : holds
    · have equal : (fun value => holds → set value) = set :=
        funext fun value => propext ⟨fun implied => implied inside, fun member _ => member⟩
      rw [equal]
      exact measurable inside
    · have equal : (fun value => holds → set value) = Set.univ :=
        funext fun value => propext ⟨fun _ => True.intro, fun _ held => absurd held inside⟩
      rw [equal]
      exact space.univ
  refine ⟨leftKeys ++ rightKeys,
    fun key value => (key ∈ leftKeys → leftSets key value) ∧ (key ∈ rightKeys → rightSets key value),
    fun key _ => space.inter (piece _ _ (leftMeasurable key)) (piece _ _ (rightMeasurable key)), ?_⟩
  apply Set.ext
  intro point
  constructor
  · rintro ⟨inLeft, inRight⟩ key _
    exact ⟨fun member => inLeft key member, fun member => inRight key member⟩
  · intro inside
    exact ⟨fun key member => (inside key (List.mem_append.mpr (Or.inl member))).1 member,
      fun key member => (inside key (List.mem_append.mpr (Or.inr member))).2 member⟩

theorem cylinders_univ : cylinders ι space Set.univ :=
  ⟨[], fun _ => Set.univ, fun _ member => (nomatch member), (cylinder_nil _).symm⟩

theorem cylinders_generate :
    Space.pi (fun _ : ι => space) = Space.generated (cylinders ι space) := by
  apply Space.ext
  intro set
  constructor
  · intro measurable
    refine Space.generated_minimal (generators := Space.PiGenerator fun _ : ι => space)
      (Space.generated (cylinders ι space)) ?_ measurable
    intro basic member
    obtain ⟨key, coordinate, coordinateMeasurable, rfl⟩ := member
    exact Space.generated_contains
      ⟨[key], fun _ => coordinate, fun _ _ => coordinateMeasurable, (cylinder_single key coordinate).symm⟩
  · intro measurable
    refine Space.generated_minimal (generators := cylinders ι space)
      (Space.pi fun _ : ι => space) ?_ measurable
    intro basic member
    obtain ⟨keys, sets, setsMeasurable, rfl⟩ := member
    exact cylinder_measurable setsMeasurable

/-- A class of measurable sets on which finite measures are determined. -/
@[expose] def Determining (space : Space α) (generator : Set (Set α)) : Prop :=
  (∀ set, generator set → space.Measurable set) ∧
    ∀ left right : Measure space, left.IsFinite → right.IsFinite →
      (∀ set, generator set → left set = right set) → left = right

/-- A generating pi-system that contains the whole space determines finite
measures. -/
theorem Determining.of_generate {generator : Set (Set α)}
    (generates : space = Space.generated generator) (pi : PiSystem generator)
    (containsUniv : generator Set.univ) : Determining space generator := by
  refine ⟨fun set member => ?_, fun left right leftFinite rightFinite agree =>
    Measure.ext_of_generate generator generates pi containsUniv leftFinite rightFinite agree⟩
  rw [generates]
  exact Space.generated_contains member

/-- Points determine measures on a discrete space that injects into the
naturals: each set is the disjoint union of its points, one per code. -/
theorem Determining.singletons (code : α → Nat) (injective : Function.Injective code) :
    Determining (Space.discrete α) (fun set => ∃ point, set = Set.singleton point) := by
  classical
  refine ⟨fun set _ => Space.discrete_measurable set, fun left right _ _ agree => ?_⟩
  apply Measure.ext
  intro set _
  let pieces : Nat → Set α := fun index point => set point ∧ code point = index
  have piece (index : Nat) : pieces index = Set.empty ∨ ∃ point, pieces index = Set.singleton point := by
    by_cases found : ∃ point, set point ∧ code point = index
    · obtain ⟨point, member, coded⟩ := found
      refine Or.inr ⟨point, Set.ext fun other => ⟨fun inside => ?_, fun same => ?_⟩⟩
      · exact injective (inside.2.trans coded.symm)
      · change other = point at same
        subst same
        exact ⟨member, coded⟩
    · exact Or.inl (Set.ext fun other => ⟨fun inside => found ⟨other, inside⟩, False.elim⟩)
  have pieceMeasurable (index : Nat) : (Space.discrete α).Measurable (pieces index) :=
    Space.discrete_measurable _
  have pieceEqual (index : Nat) : left (pieces index) = right (pieces index) := by
    rcases piece index with empty | ⟨point, single⟩
    · rw [empty, Measure.empty_apply, Measure.empty_apply]
    · rw [single]
      exact agree _ ⟨point, rfl⟩
  have disjoint : Set.PairwiseDisjoint pieces := fun _ _ different _ first second =>
    different (first.2.symm.trans second.2)
  have union : set = Set.iUnion pieces :=
    Set.ext fun point => ⟨fun member => ⟨code point, member, rfl⟩, fun ⟨_, inside⟩ => inside.1⟩
  rw [union, Measure.iUnion_disjoint _ _ pieceMeasurable disjoint,
    Measure.iUnion_disjoint _ _ pieceMeasurable disjoint]
  exact ENNReal.tsum_congr pieceEqual

/-- Finite cylinders over measurable sets determine finite measures on the
product space. -/
theorem determining_cylinders :
    Determining (Space.pi fun _ : ι => space) (cylinders ι space) :=
  Determining.of_generate cylinders_generate cylinders_pi cylinders_univ

private noncomputable def update (sets : ι → Set α) (key : ι) (set : Set α) : ι → Set α :=
  fun other => @ite _ (other = key) (Classical.propDecidable _) set (sets other)

private theorem update_same (sets : ι → Set α) (key : ι) (set : Set α) :
    update sets key set key = set :=
  ite_eq_left rfl

private theorem update_other (sets : ι → Set α) {key other : ι} (set : Set α)
    (different : other ≠ key) : update sets key set other = sets other :=
  ite_eq_right different

/-- One key's step of the extension: a slice of a finite measure along one
coordinate is determined by its values on the determining class. -/
private theorem slice {measure : Measure (Space.pi fun _ : ι => space)}
    {laws : ι → Measure space} {generator : Set (Set α)} (determining : Determining space generator)
    (lawsFinite : ∀ key, (laws key).IsFinite) (measureFinite : measure.IsFinite)
    (key : ι) (region : Set (ι → α)) (factor : ENNReal) (factorFinite : ENNReal.Finite factor)
    (agree : ∀ set, generator set →
      measure (Set.inter (Set.preimage (fun point => point key) set) region) =
        ENNReal.mul (laws key set) factor)
    {set : Set α} (measurable : space.Measurable set) :
    measure (Set.inter (Set.preimage (fun point => point key) set) region) =
      ENNReal.mul (laws key set) factor := by
  have equal : (measure.restrict region).map (fun point => point key)
      (Space.coordinate_measurable (fun _ : ι => space) key) = Measure.smul factor (laws key) := by
    apply determining.2 _ _ ((measureFinite.restrict region).map _ _)
      (Measure.IsFinite.smul factor factorFinite (lawsFinite key))
    intro basic generated
    have basicMeasurable := determining.1 basic generated
    rw [Measure.map_apply _ _ _ basicMeasurable,
      Measure.restrict_apply _ _
        (Space.coordinate_measurable (fun _ : ι => space) key basicMeasurable),
      Measure.smul_apply_measurable _ _ basicMeasurable, agree basic generated, ENNReal.mul_comm]
  have atSet : ((measure.restrict region).map (fun point => point key)
      (Space.coordinate_measurable (fun _ : ι => space) key)) set =
        (Measure.smul factor (laws key)) set := by
    rw [equal]
  rw [Measure.map_apply _ _ _ measurable,
    Measure.restrict_apply _ _ (Space.coordinate_measurable (fun _ : ι => space) key measurable),
    Measure.smul_apply_measurable _ _ measurable] at atSet
  rw [atSet, ENNReal.mul_comm]

/-- `point` with the coordinate at `key` replaced by `value`. -/
@[expose] noncomputable def replace (point : ι → α) (key : ι) (value : α) : ι → α :=
  fun other => @ite _ (other = key) (Classical.propDecidable _) value (point other)

theorem replace_same (point : ι → α) (key : ι) (value : α) :
    replace point key value key = value :=
  ite_eq_left rfl

theorem replace_other (point : ι → α) {key other : ι} (value : α) (different : other ≠ key) :
    replace point key value other = point other :=
  ite_eq_right different

/-- Writing a coordinate's own value over it changes nothing. -/
theorem replace_self (point : ι → α) (key : ι) : replace point key (point key) = point := by
  funext other
  by_cases same : other = key
  · rw [same, replace_same]
  · exact replace_other point _ same

/-- A function applied after replacing is the replacement of its applications. -/
theorem apply_replace {β : Type w} (function : α → β) (point : ι → α) (key : ι) (value : α) :
    (fun other => function (replace point key value other)) =
      replace (fun other => function (point other)) key (function value) := by
  funext other
  by_cases same : other = key
  · rw [same, replace_same, replace_same]
  · rw [replace_other _ _ same, replace_other _ _ same]

/-- Overwriting one coordinate with a second argument is measurable. -/
theorem replace_measurable (key : ι) :
    MeasurableMap (Space.product (Space.pi fun _ : ι => space) space)
      (Space.pi fun _ : ι => space) (fun pair => replace pair.1 key pair.2) := by
  refine Space.pi_measurable fun other => ?_
  by_cases same : other = key
  · have reads : (fun pair : (ι → α) × α => replace pair.1 key pair.2 other) = Prod.snd := by
      funext pair
      rw [same, replace_same]
    rw [reads]
    exact Space.second_measurable _ _
  · have reads : (fun pair : (ι → α) × α => replace pair.1 key pair.2 other) =
        fun pair => pair.1 other :=
      funext fun pair => replace_other pair.1 pair.2 same
    rw [reads]
    exact MeasurableMap.comp (Space.coordinate_measurable (fun _ : ι => space) other)
      (Space.first_measurable _ _)

/-- The positions after `0` that a list of `Fin (n + 1)` names, shifted down. -/
private def tails {n : Nat} (keys : List (Fin (n + 1))) : List (Fin n) :=
  keys.filterMap fun key => Fin.cases none some key

private theorem mem_tails {n : Nat} {keys : List (Fin (n + 1))} {position : Fin n} :
    position ∈ tails keys ↔ position.succ ∈ keys := by
  unfold tails
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨key, member, found⟩
    induction key using Fin.cases with
    | zero => simp at found
    | succ other =>
        simp only [Fin.cases_succ, Option.some.injEq] at found
        exact found ▸ member
  · intro member
    exact ⟨position.succ, member, by simp⟩

private theorem tails_nodup {n : Nat} {keys : List (Fin (n + 1))} (distinct : keys.Nodup) :
    (tails keys).Nodup := by
  refine List.Pairwise.filterMap _ (fun first second different position atFirst other atSecond
    same => different ?_) distinct
  induction first using Fin.cases with
  | zero => simp at atFirst
  | succ first =>
      induction second using Fin.cases with
      | zero => simp at atSecond
      | succ second =>
          simp only [Fin.cases_succ, Option.some.injEq] at atFirst atSecond
          rw [atFirst, atSecond, same]

/-- A list of `Fin (n + 1)` that misses `0` is its tails shifted up. -/
private theorem map_succ_tails {n : Nat} :
    (keys : List (Fin (n + 1))) → (0 : Fin (n + 1)) ∉ keys → (tails keys).map Fin.succ = keys
  | [], _ => rfl
  | key :: rest, missing => by
      have restMissing : (0 : Fin (n + 1)) ∉ rest := fun member => missing (List.Mem.tail _ member)
      induction key using Fin.cases with
      | zero => exact absurd (List.Mem.head _) missing
      | succ position =>
          change (List.filterMap _ (position.succ :: rest)).map Fin.succ = _
          rw [List.filterMap_cons_some (b := position) (by simp), List.map_cons]
          exact congrArg (List.cons position.succ) (map_succ_tails rest restMissing)

private theorem tails_append_zero {n : Nat} (before after : List (Fin (n + 1))) :
    tails (before ++ 0 :: after) = tails (before ++ after) := by
  unfold tails
  rw [List.filterMap_append, List.filterMap_cons_none (by simp), List.filterMap_append]

namespace IsProduct

variable {measure : Measure (Space.pi fun _ : ι => space)} {laws : ι → Measure space}

/-- The product shape depends on the laws only through their values. -/
theorem congr_laws (product : IsProduct measure laws) {other : ι → Measure space}
    (same : ∀ key, laws key = other key) : IsProduct measure other := by
  intro keys distinctKeys sets measurable
  rw [product keys distinctKeys sets measurable]
  exact massProduct_congr fun key _ => by rw [same key]

/-- A product law has total mass one: the cylinder over no keys is everything. -/
theorem probability (product : IsProduct measure laws) : measure.IsProbability := by
  constructor
  have total := product [] List.nodup_nil (fun _ => Set.univ) (fun _ member => (nomatch member))
  rw [cylinder_nil] at total
  exact total

/-- Each coordinate of a product law has its own law. -/
theorem coordinate (product : IsProduct measure laws) (key : ι) :
    measure.map (fun point => point key) (Space.coordinate_measurable (fun _ : ι => space) key) =
      laws key := by
  apply Measure.ext
  intro set measurable
  rw [Measure.map_apply _ _ _ measurable, ← cylinder_single key set,
    product [key] (List.nodup_cons.mpr ⟨fun member => (nomatch member), List.nodup_nil⟩)
      (fun _ => set) (fun _ _ => measurable),
    massProduct_cons, massProduct_nil, ENNReal.mul_one]

/-- Every coordinate law of a product law has total mass one. -/
theorem law_probability (product : IsProduct measure laws) (key : ι) :
    (laws key).IsProbability := by
  rw [← product.coordinate key]
  exact product.probability.map _ _

/-- Distinct coordinates of a product law are independent: a joint event on two
of them has the product of their masses. -/
theorem pair (product : IsProduct measure laws) {first second : ι} (different : first ≠ second)
    {firstSet secondSet : Set α} (firstMeasurable : space.Measurable firstSet)
    (secondMeasurable : space.Measurable secondSet) :
    measure (fun point => firstSet (point first) ∧ secondSet (point second)) =
      ENNReal.mul (laws first firstSet) (laws second secondSet) := by
  let sets := update (fun _ => secondSet) first firstSet
  have atFirst : sets first = firstSet := update_same _ _ _
  have atSecond : sets second = secondSet := update_other _ _ (Ne.symm different)
  have equal : (fun point : ι → α => firstSet (point first) ∧ secondSet (point second)) =
      cylinder [first, second] sets := by
    rw [cylinder_cons, cylinder_cons, cylinder_nil, Set.inter_univ_right, atFirst, atSecond]
    rfl
  have distinctKeys : [first, second].Nodup :=
    List.nodup_cons.mpr ⟨fun member => different (List.mem_singleton.mp member),
      List.nodup_cons.mpr ⟨fun member => (nomatch member), List.nodup_nil⟩⟩
  have measurable : ∀ key ∈ [first, second], space.Measurable (sets key) := by
    intro key member
    rcases List.mem_cons.mp member with same | rest
    · rw [same, atFirst]
      exact firstMeasurable
    · rw [List.mem_singleton.mp rest, atSecond]
      exact secondMeasurable
  rw [equal, product [first, second] distinctKeys sets measurable, massProduct_cons,
    massProduct_cons, massProduct_nil, ENNReal.mul_one, atFirst, atSecond]

/-- Distinct coordinates of a product law are independent: their joint law is
the product measure of their laws. -/
theorem pair_prod (product : IsProduct measure laws) {first second : ι}
    (different : first ≠ second) :
    measure.map (fun point => (point first, point second))
        (Space.pair_measurable (Space.coordinate_measurable (fun _ : ι => space) first)
          (Space.coordinate_measurable (fun _ : ι => space) second)) =
      Measure.prod (laws first) (laws second)
        (Measure.SigmaFinite.ofFinite (product.law_probability second).to_finite).toSFinite :=
  Measure.prod_unique (Measure.SigmaFinite.ofFinite (product.law_probability first).to_finite)
    (Measure.SigmaFinite.ofFinite (product.law_probability second).to_finite)
    fun firstSet secondSet firstMeasurable secondMeasurable => by
      rw [Measure.map_apply _ _ _
        (Space.product_set_measurable _ _ firstMeasurable secondMeasurable)]
      exact product.pair different firstMeasurable secondMeasurable

/-- A product law is unique. -/
theorem ext {left right : Measure (Space.pi fun _ : ι => space)}
    (leftProduct : IsProduct left laws) (rightProduct : IsProduct right laws) : left = right := by
  apply Measure.ext_of_generate (cylinders ι space) cylinders_generate cylinders_pi cylinders_univ
    leftProduct.probability.to_finite rightProduct.probability.to_finite
  intro set member
  obtain ⟨keys, sets, measurable, rfl⟩ := member
  have distinctMeasurable : ∀ key ∈ distinct keys, space.Measurable (sets key) :=
    fun key member => measurable key (mem_distinct.mp member)
  rw [← cylinder_distinct keys sets,
    leftProduct _ (nodup_distinct keys) sets distinctMeasurable,
    rightProduct _ (nodup_distinct keys) sets distinctMeasurable]

/-- Product masses on cylinders over a determining class extend to all
measurable cylinders, one key at a time. -/
theorem of_determining {generator : Set (Set α)} (determining : Determining space generator)
    (lawsFinite : ∀ key, (laws key).IsFinite)
    (agree : ∀ keys : List ι, keys.Nodup → ∀ sets : ι → Set α,
      (∀ key ∈ keys, generator (sets key)) →
        measure (cylinder keys sets) = massProduct keys fun key => laws key (sets key)) :
    IsProduct measure laws := by
  have total : measure Set.univ = ENNReal.one := by
    have whole := agree [] List.nodup_nil (fun _ => Set.univ) (fun _ member => (nomatch member))
    rw [cylinder_nil] at whole
    exact whole
  have measureFinite : measure.IsFinite := ⟨by rw [total]; exact True.intro⟩
  have upgrade : ∀ upgraded basic : List ι, (upgraded ++ basic).Nodup → ∀ sets : ι → Set α,
      (∀ key ∈ upgraded, space.Measurable (sets key)) → (∀ key ∈ basic, generator (sets key)) →
      measure (cylinder (upgraded ++ basic) sets) =
        massProduct (upgraded ++ basic) fun key => laws key (sets key) := by
    intro upgraded
    induction upgraded with
    | nil => exact fun basic distinctKeys sets _ generated => agree basic distinctKeys sets generated
    | cons key rest induction =>
        intro basic distinctKeys sets measurable generated
        have distinctCons : (key :: (rest ++ basic)).Nodup := distinctKeys
        have fresh : key ∉ rest ++ basic := (List.nodup_cons.mp distinctCons).1
        have moved : (rest ++ key :: basic).Nodup := distinctCons.perm List.perm_middle.symm
        have different : ∀ other ∈ rest ++ basic, other ≠ key :=
          fun other member same => fresh (same ▸ member)
        have reshape : ∀ set : Set α,
            Set.inter (Set.preimage (fun point : ι → α => point key) set) (cylinder (rest ++ basic) sets) =
              cylinder (rest ++ key :: basic) (update sets key set) := by
          intro set
          apply Set.ext
          intro point
          constructor
          · rintro ⟨atKey, inside⟩ other member
            by_cases same : other = key
            · rw [same, update_same]
              exact atKey
            · rw [update_other _ _ same]
              apply inside other
              rcases List.mem_append.mp member with inRest | inTail
              · exact List.mem_append.mpr (Or.inl inRest)
              · rcases List.mem_cons.mp inTail with isKey | inBasic
                · exact absurd isKey same
                · exact List.mem_append.mpr (Or.inr inBasic)
          · intro inside
            refine ⟨?_, fun other member => ?_⟩
            · have atKey := inside key (List.mem_append.mpr (Or.inr (List.Mem.head _)))
              rw [update_same] at atKey
              exact atKey
            · have atOther := inside other (by
                rcases List.mem_append.mp member with inRest | inBasic
                · exact List.mem_append.mpr (Or.inl inRest)
                · exact List.mem_append.mpr (Or.inr (List.Mem.tail _ inBasic)))
              rw [update_other _ _ (different other member)] at atOther
              exact atOther
        have factorFinite :
            ENNReal.Finite (massProduct (rest ++ basic) fun other => laws other (sets other)) :=
          massProduct_finite fun other _ => (lawsFinite other).apply _
        have agreeSlice : ∀ set, generator set →
            measure (Set.inter (Set.preimage (fun point => point key) set)
              (cylinder (rest ++ basic) sets)) =
              ENNReal.mul (laws key set)
                (massProduct (rest ++ basic) fun other => laws other (sets other)) := by
          intro set generatedSet
          have restMeasurable : ∀ other ∈ rest, space.Measurable (update sets key set other) := by
            intro other member
            rw [update_other _ _ (different other (List.mem_append.mpr (Or.inl member)))]
            exact measurable other (List.Mem.tail _ member)
          have basicGenerated : ∀ other ∈ key :: basic, generator (update sets key set other) := by
            intro other member
            rcases List.mem_cons.mp member with same | inBasic
            · rw [same, update_same]
              exact generatedSet
            · rw [update_other _ _ (different other (List.mem_append.mpr (Or.inr inBasic)))]
              exact generated other inBasic
          rw [reshape set, induction (key :: basic) moved (update sets key set) restMeasurable
            basicGenerated, massProduct_middle, update_same]
          exact congrArg (ENNReal.mul (laws key set)) (massProduct_congr fun other member => by
            rw [update_other _ _ (different other member)])
        have stepped := slice determining lawsFinite measureFinite key (cylinder (rest ++ basic) sets)
          _ factorFinite agreeSlice (measurable key (List.Mem.head _))
        rw [List.cons_append, cylinder_cons, stepped, massProduct_cons]
  intro keys distinctKeys sets measurable
  have whole := upgrade keys [] (by rw [List.append_nil]; exact distinctKeys) sets measurable
    (fun _ member => (nomatch member))
  rw [List.append_nil] at whole
  exact whole

/-- Coordinatewise measurable maps keep the product shape, with each law pushed
through its own map. -/
theorem map {β : Type w} {target : Space β} (product : IsProduct measure laws)
    (functions : ι → α → β) (measurable : ∀ key, MeasurableMap space target (functions key)) :
    IsProduct (measure.map (fun point key => functions key (point key)) (Space.pi_map measurable))
      (fun key => (laws key).map (functions key) (measurable key)) := by
  intro keys distinctKeys sets setsMeasurable
  rw [Measure.map_apply _ _ _ (cylinder_measurable setsMeasurable)]
  have equal := product keys distinctKeys (fun key => Set.preimage (functions key) (sets key))
    (fun key member => measurable key (setsMeasurable key member))
  exact equal.trans (massProduct_congr fun key member =>
    (Measure.map_apply _ _ _ (setsMeasurable key member)).symm)

/-- Reading the coordinates along an injection keeps the product shape. -/
theorem reindex {κ : Type w} (product : IsProduct measure laws) (encode : κ → ι)
    (injective : Function.Injective encode) :
    IsProduct (measure.map (fun point key => point (encode key))
        (Space.pi_reindex (fun _ : ι => space) encode))
      (fun key => laws (encode key)) := by
  intro keys distinctKeys sets setsMeasurable
  rw [Measure.map_apply _ _ _ (cylinder_measurable setsMeasurable)]
  let coded : ι → Set α := fun index value => ∀ key, encode key = index → sets key value
  have codedAt : ∀ key, coded (encode key) = sets key := fun key =>
    funext fun value => propext ⟨fun inside => inside key rfl,
      fun inside other same => (injective same) ▸ inside⟩
  have equal : Set.preimage (fun point : ι → α => fun key => point (encode key))
      (cylinder keys sets) = cylinder (keys.map encode) coded := by
    apply Set.ext
    intro point
    constructor
    · intro inside index member
      obtain ⟨key, inKeys, rfl⟩ := List.mem_map.mp member
      rw [codedAt]
      exact inside key inKeys
    · intro inside key member
      have atKey := inside (encode key) (List.mem_map_of_mem member)
      rw [codedAt] at atKey
      exact atKey
  have distinctCoded : (keys.map encode).Nodup :=
    List.Pairwise.map encode
      (fun first second (different : first ≠ second) (same : encode first = encode second) =>
        different (injective same)) distinctKeys
  have codedMeasurable : ∀ index ∈ keys.map encode, space.Measurable (coded index) := by
    intro index member
    obtain ⟨key, inKeys, rfl⟩ := List.mem_map.mp member
    rw [codedAt]
    exact setsMeasurable key inKeys
  rw [equal, product _ distinctCoded coded codedMeasurable, massProduct_map]
  exact massProduct_congr fun key _ => by rw [codedAt]

/-- Regrouping the coordinates into blocks along an injective coding keeps the
product shape: the blocks are independent, and each block has the law of its
own coordinates. -/
theorem blocks {β : Type w} {γ : Type x} (product : IsProduct measure laws)
    (encode : β → γ → ι)
    (injective : ∀ block index other position,
      encode block index = encode other position → block = other ∧ index = position) :
    IsProduct (space := Space.pi fun _ : γ => space)
      (measure.map (fun point block index => point (encode block index))
        (Space.pi_measurable fun block => Space.pi_reindex (fun _ : ι => space) (encode block)))
      (fun block => measure.map (fun point index => point (encode block index))
        (Space.pi_reindex (fun _ : ι => space) (encode block))) := by
  apply of_determining determining_cylinders
    (fun block => product.probability.to_finite.map _ _)
  intro keys distinctKeys sets generated
  have choice : ∀ block, ∃ data : List γ × (γ → Set α), data.1.Nodup ∧
      (block ∈ keys → (∀ index ∈ data.1, space.Measurable (data.2 index)) ∧
        sets block = cylinder data.1 data.2) := by
    intro block
    by_cases member : block ∈ keys
    · obtain ⟨rowKeys, rowSets, measurable, equal⟩ := generated block member
      exact ⟨(distinct rowKeys, rowSets), nodup_distinct rowKeys, fun _ =>
        ⟨fun index inside => measurable index (mem_distinct.mp inside),
          equal.trans (cylinder_distinct rowKeys rowSets).symm⟩⟩
    · exact ⟨([], fun _ => Set.univ), List.nodup_nil, fun inside => absurd inside member⟩
  obtain ⟨chosen, chosenSpec⟩ := Classical.axiomOfChoice choice
  have rowInjective : ∀ block, Function.Injective (encode block) :=
    fun block _ _ same => (injective _ _ _ _ same).2
  let coded : ι → Set α := fun key value =>
    ∀ block index, encode block index = key → (chosen block).2 index value
  have codedAt : ∀ block index, coded (encode block index) = (chosen block).2 index :=
    fun block index => funext fun value => propext ⟨fun inside => inside block index rfl,
      fun inside other position same => by
        obtain ⟨sameBlock, samePosition⟩ := injective _ _ _ _ same
        subst sameBlock
        subst samePosition
        exact inside⟩
  have distinctFlat : (keys.flatMap fun block => (chosen block).1.map (encode block)).Nodup := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun block _ => List.Pairwise.map (encode block)
      (fun first second (different : first ≠ second)
        (same : encode block first = encode block second) => different (rowInjective block same))
      (chosenSpec block).1, ?_⟩
    refine List.Pairwise.imp (fun {block other} (different : block ≠ other) => ?_) distinctKeys
    intro key inBlock otherKey inOther same
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp inBlock
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp inOther
    exact different (injective _ _ _ _ same).1
  have flatMeasurable : ∀ key ∈ keys.flatMap (fun block => (chosen block).1.map (encode block)),
      space.Measurable (coded key) := by
    intro key member
    obtain ⟨block, inKeys, inBlock⟩ := List.mem_flatMap.mp member
    obtain ⟨index, inChosen, rfl⟩ := List.mem_map.mp inBlock
    rw [codedAt]
    exact ((chosenSpec block).2 inKeys).1 index inChosen
  have equal : Set.preimage (fun point : ι → α => fun block index => point (encode block index))
      (cylinder keys sets) =
        cylinder (keys.flatMap fun block => (chosen block).1.map (encode block)) coded := by
    apply Set.ext
    intro point
    constructor
    · intro inside key member
      obtain ⟨block, inKeys, inBlock⟩ := List.mem_flatMap.mp member
      obtain ⟨index, inChosen, rfl⟩ := List.mem_map.mp inBlock
      have atBlock := inside block inKeys
      rw [((chosenSpec block).2 inKeys).2] at atBlock
      rw [codedAt]
      exact atBlock index inChosen
    · intro inside block inKeys
      change sets block (fun index => point (encode block index))
      rw [((chosenSpec block).2 inKeys).2]
      intro index inChosen
      have atKey := inside (encode block index)
        (List.mem_flatMap.mpr ⟨block, inKeys, List.mem_map_of_mem inChosen⟩)
      rw [codedAt] at atKey
      exact atKey
  rw [Measure.map_apply _ _ _
      (cylinder_measurable fun block member => determining_cylinders.1 _ (generated block member)),
    equal, product _ distinctFlat coded flatMeasurable, massProduct_flatMap]
  refine massProduct_congr fun block inKeys => ?_
  rw [((chosenSpec block).2 inKeys).2,
    (product.reindex (encode block) (rowInjective block)) _ (chosenSpec block).1 _
      ((chosenSpec block).2 inKeys).1, massProduct_map]
  exact massProduct_congr fun index _ => by rw [codedAt]

/-- Independent rows with independent entries form the product over pair keys. -/
theorem uncurry {κ : Type w}
    {outer : Measure (Space.pi fun _ : κ => Space.pi fun _ : ι => space)}
    {rows : κ → Measure (Space.pi fun _ : ι => space)} {entries : κ → ι → Measure space}
    (rowProduct : IsProduct outer rows) (entryProduct : ∀ row, IsProduct (rows row) (entries row))
    (measurable : MeasurableMap (Space.pi fun _ : κ => Space.pi fun _ : ι => space)
      (Space.pi fun _ : κ × ι => space) (fun table key => table key.1 key.2)) :
    IsProduct (outer.map (fun table (key : κ × ι) => table key.1 key.2) measurable)
      (fun (key : κ × ι) => entries key.1 key.2) := by
  classical
  intro keys distinctKeys sets setsMeasurable
  let blocks := distinct (keys.map Prod.fst)
  let positions := fun block => keys.filterMap fun key =>
    if key.1 = block then some key.2 else none
  have found : ∀ (block : κ) (key : κ × ι) (index : ι),
      (if key.1 = block then some key.2 else none) = some index ↔ key = (block, index) := by
    intro block key index
    by_cases same : key.1 = block
    · simp only [same, ite_true, Option.some.injEq]
      exact ⟨fun equal => Prod.ext same equal, fun equal => congrArg Prod.snd equal⟩
    · simp only [same, ite_false, reduceCtorEq, false_iff]
      exact fun equal => same (congrArg Prod.fst equal)
  have member : ∀ block index, index ∈ positions block ↔ (block, index) ∈ keys := by
    intro block index
    simp only [positions, List.mem_filterMap, found]
    exact ⟨fun ⟨_, inside, equal⟩ => equal ▸ inside, fun inside => ⟨_, inside, rfl⟩⟩
  have rowDistinct : ∀ block, (positions block).Nodup := by
    intro block
    refine List.Pairwise.filterMap _ (fun first second different index atFirst other atSecond same => ?_)
      distinctKeys
    exact different ((found block first index).mp atFirst |>.trans
      ((congrArg (fun index => (block, index)) same).trans ((found block second other).mp atSecond).symm))
  let flattened := blocks.flatMap fun block => (positions block).map fun index => (block, index)
  have flatDistinct : flattened.Nodup := by
    refine List.pairwise_flatMap.mpr ⟨fun block _ => ?_, ?_⟩
    · exact List.Pairwise.map _ (fun _ _ different same => different (congrArg Prod.snd same))
        (rowDistinct block)
    · refine (nodup_distinct _).imp (fun {block other} (different : block ≠ other) => ?_)
      intro first inFirst second inSecond same
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp inFirst
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp inSecond
      exact different (congrArg Prod.fst same)
  have reordered : flattened.Perm keys := (List.perm_ext_iff_of_nodup flatDistinct distinctKeys).mpr
    fun key => by
      simp only [flattened, List.mem_flatMap, List.mem_map, member]
      constructor
      · rintro ⟨block, _, index, inside, equal⟩
        exact equal ▸ inside
      · intro inside
        exact ⟨key.1, mem_distinct.mpr (List.mem_map_of_mem inside), key.2, inside, rfl⟩
  have rowMeasurable : ∀ block, ∀ index ∈ positions block, space.Measurable (sets (block, index)) :=
    fun block index inside => setsMeasurable _ ((member block index).mp inside)
  have pullback : Set.preimage (fun table key => table key.1 key.2) (cylinder keys sets) =
      cylinder blocks (fun block => cylinder (positions block) (fun index => sets (block, index))) := by
    apply Set.ext
    intro table
    constructor
    · intro inside block _ index atIndex
      exact inside _ ((member block index).mp atIndex)
    · intro inside key atKey
      exact inside key.1 (mem_distinct.mpr (List.mem_map_of_mem atKey)) key.2
        ((member key.1 key.2).mpr atKey)
  rw [Measure.map_apply _ _ _ (cylinder_measurable setsMeasurable), pullback,
    rowProduct blocks (nodup_distinct _) _ (fun block _ => cylinder_measurable (rowMeasurable block))]
  calc
    _ = massProduct blocks (fun block => massProduct (positions block)
        (fun index => entries block index (sets (block, index)))) :=
      massProduct_congr fun block _ => entryProduct block _ (rowDistinct block) _ (rowMeasurable block)
    _ = massProduct flattened (fun key => entries key.1 key.2 (sets key)) := by
      dsimp only [flattened]
      rw [massProduct_flatMap]
      exact massProduct_congr fun block _ => (massProduct_map
        (fun index => (block, index)) (positions block)
        (fun key => entries key.1 key.2 (sets key))).symm
    _ = _ := massProduct_perm reordered _

/-- The independent pair of two products is the product over their sum keys. -/
theorem sum {κ : Type w} {left : Measure (Space.pi fun _ : ι => space)}
    {right : Measure (Space.pi fun _ : κ => space)}
    {leftLaws : ι → Measure space} {rightLaws : κ → Measure space}
    (leftProduct : IsProduct left leftLaws) (rightProduct : IsProduct right rightLaws)
    (measurable : MeasurableMap
      (Space.product (Space.pi fun _ : ι => space) (Space.pi fun _ : κ => space))
      (Space.pi fun _ : ι ⊕ κ => space) (fun pair => Sum.elim pair.1 pair.2)) :
    IsProduct ((Measure.prod left right (Measure.SigmaFinite.ofFinite rightProduct.probability.to_finite).toSFinite).map
      (fun pair => Sum.elim pair.1 pair.2) measurable) (Sum.elim leftLaws rightLaws) := by
  intro keys distinctKeys sets setsMeasurable
  have leftMember : ∀ key, key ∈ keys.filterMap Sum.getLeft? ↔ Sum.inl key ∈ keys := by
    intro key
    simp only [List.mem_filterMap, Sum.getLeft?_eq_some_iff]
    exact ⟨fun ⟨_, inside, equal⟩ => equal ▸ inside, fun inside => ⟨_, inside, rfl⟩⟩
  have rightMember : ∀ key, key ∈ keys.filterMap Sum.getRight? ↔ Sum.inr key ∈ keys := by
    intro key
    simp only [List.mem_filterMap, Sum.getRight?_eq_some_iff]
    exact ⟨fun ⟨_, inside, equal⟩ => equal ▸ inside, fun inside => ⟨_, inside, rfl⟩⟩
  have leftDistinct : (keys.filterMap Sum.getLeft?).Nodup :=
    List.Pairwise.filterMap _ (fun first second different index atFirst other atSecond same =>
      different ((Sum.getLeft?_eq_some_iff.mp atFirst).trans
        ((congrArg Sum.inl same).trans (Sum.getLeft?_eq_some_iff.mp atSecond).symm))) distinctKeys
  have rightDistinct : (keys.filterMap Sum.getRight?).Nodup :=
    List.Pairwise.filterMap _ (fun first second different index atFirst other atSecond same =>
      different ((Sum.getRight?_eq_some_iff.mp atFirst).trans
        ((congrArg Sum.inr same).trans (Sum.getRight?_eq_some_iff.mp atSecond).symm))) distinctKeys
  have leftMeasurable := fun key inside => setsMeasurable (Sum.inl key) ((leftMember key).mp inside)
  have rightMeasurable := fun key inside => setsMeasurable (Sum.inr key) ((rightMember key).mp inside)
  have pullback : Set.preimage (fun pair => Sum.elim pair.1 pair.2) (cylinder keys sets) =
      Set.product (cylinder (keys.filterMap Sum.getLeft?) (fun key => sets (.inl key)))
        (cylinder (keys.filterMap Sum.getRight?) (fun key => sets (.inr key))) := by
    apply Set.ext
    intro pair
    constructor
    · intro inside
      exact ⟨fun key member => inside _ ((leftMember key).mp member),
        fun key member => inside _ ((rightMember key).mp member)⟩
    · rintro ⟨first, second⟩ key member
      cases key with
      | inl key => exact first key ((leftMember key).mpr member)
      | inr key => exact second key ((rightMember key).mpr member)
  rw [Measure.map_apply _ _ _ (cylinder_measurable setsMeasurable), pullback,
    Measure.prod_apply_product _ _ _ (cylinder_measurable leftMeasurable)
      (cylinder_measurable rightMeasurable),
    leftProduct _ leftDistinct _ leftMeasurable, rightProduct _ rightDistinct _ rightMeasurable]
  have partition : ∀ keys : List (ι ⊕ κ),
      ((keys.filterMap Sum.getLeft?).map Sum.inl ++
        (keys.filterMap Sum.getRight?).map Sum.inr).Perm keys := by
    intro keys
    induction keys with
    | nil => exact List.Perm.nil
    | cons key rest induction =>
        cases key <;> simp only [List.filterMap_cons, Sum.getLeft?, Sum.getRight?,
          List.map_cons, List.cons_append]
        · exact List.Perm.cons _ induction
        · exact List.perm_middle.trans (List.Perm.cons _ induction)
  calc
    _ = massProduct ((keys.filterMap Sum.getLeft?).map Sum.inl ++
        (keys.filterMap Sum.getRight?).map Sum.inr)
        (fun key => Sum.elim leftLaws rightLaws key (sets key)) := by
      rw [massProduct_append, massProduct_map, massProduct_map]
      rfl
    _ = _ := massProduct_perm (partition keys) _


/-! ### Redrawing one coordinate, and prepending one -/

/-- Redrawing one coordinate from its own law, independently of the rest, and
writing it over the old one leaves a product law where it was. -/
theorem update (product : IsProduct measure laws) (key : ι) (finite : Measure.SFinite (laws key)) :
    (Measure.prod measure (laws key) finite).map (fun pair => replace pair.1 key pair.2)
        (replace_measurable key) = measure := by
  refine ext ?_ product
  intro keys distinctKeys sets measurable
  rw [Measure.map_apply _ _ _ (cylinder_measurable measurable)]
  by_cases member : key ∈ keys
  · obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    have split := List.nodup_append.mp distinctKeys
    have afterSplit := List.nodup_cons.mp split.2.1
    have restDistinct : (before ++ after).Nodup :=
      List.nodup_append.mpr ⟨split.1, afterSplit.2, fun first inBefore second inAfter =>
        split.2.2 first inBefore second (List.Mem.tail _ inAfter)⟩
    have widen : ∀ other ∈ before ++ after, other ∈ before ++ key :: after := by
      intro other inside
      rcases List.mem_append.mp inside with inBefore | inAfter
      · exact List.mem_append_left _ inBefore
      · exact List.mem_append_right _ (List.Mem.tail _ inAfter)
    have fresh : ∀ other ∈ before ++ after, other ≠ key := by
      intro other inside
      rcases List.mem_append.mp inside with inBefore | inAfter
      · exact split.2.2 other inBefore key (List.Mem.head _)
      · exact fun same => afterSplit.1 (same ▸ inAfter)
    have restMeasurable : ∀ other ∈ before ++ after, space.Measurable (sets other) :=
      fun other inside => measurable other (widen other inside)
    have keyMeasurable := measurable key (List.mem_append_right _ (List.Mem.head _))
    have equal : Set.preimage (fun pair : (ι → α) × α => replace pair.1 key pair.2)
        (cylinder (before ++ key :: after) sets) =
          Set.product (cylinder (before ++ after) sets) (sets key) := by
      apply Set.ext
      intro pair
      constructor
      · intro inside
        refine ⟨fun other inRest => ?_, ?_⟩
        · have atOther := inside other (widen other inRest)
          change sets other (replace pair.1 key pair.2 other) at atOther
          rwa [replace_other _ _ (fresh other inRest)] at atOther
        · have atKey := inside key (List.mem_append_right _ (List.Mem.head _))
          change sets key (replace pair.1 key pair.2 key) at atKey
          rwa [replace_same] at atKey
      · rintro ⟨rest, atKey⟩ other inside
        change sets other (replace pair.1 key pair.2 other)
        by_cases same : other = key
        · rw [same, replace_same]
          exact atKey
        · rw [replace_other _ _ same]
          refine rest other ?_
          rcases List.mem_append.mp inside with inBefore | inAfter
          · exact List.mem_append_left _ inBefore
          · cases inAfter with
            | head => exact absurd rfl same
            | tail _ inAfter => exact List.mem_append_right _ inAfter
    rw [equal, Measure.prod_apply_product _ _ _ (cylinder_measurable restMeasurable) keyMeasurable,
      product _ restDistinct sets restMeasurable, massProduct_middle, ENNReal.mul_comm]
  · have away : ∀ other ∈ keys, other ≠ key := fun other inKeys same => member (same ▸ inKeys)
    have equal : Set.preimage (fun pair : (ι → α) × α => replace pair.1 key pair.2)
        (cylinder keys sets) = Set.product (cylinder keys sets) Set.univ := by
      apply Set.ext
      intro pair
      constructor
      · intro inside
        refine ⟨fun other inKeys => ?_, True.intro⟩
        have atOther := inside other inKeys
        change sets other (replace pair.1 key pair.2 other) at atOther
        rwa [replace_other _ _ (away other inKeys)] at atOther
      · rintro ⟨rest, _⟩ other inKeys
        change sets other (replace pair.1 key pair.2 other)
        rw [replace_other _ _ (away other inKeys)]
        exact rest other inKeys
    rw [equal, Measure.prod_apply_product _ _ _ (cylinder_measurable measurable) space.univ,
      product keys distinctKeys sets measurable, (product.law_probability key).univ_eq_one,
      ENNReal.mul_one]

/-- Drawing one coordinate from a new probability law, independently of the
rest, and writing it over the old one gives the product with that key's law
replaced. The new draw is the first factor, so a density on it is a density on
the first factor. -/
theorem redraw (product : IsProduct measure laws) (key : ι) {law : Measure space}
    (lawProbability : law.IsProbability) (finite : Measure.SFinite measure) :
    IsProduct ((Measure.prod law measure finite).map (fun pair => replace pair.2 key pair.1)
        (MeasurableMap.comp (replace_measurable key) (Space.swap_measurable _ _)))
      (replace laws key law) := by
  intro keys distinctKeys sets measurable
  rw [Measure.map_apply _ _ _ (cylinder_measurable measurable)]
  by_cases member : key ∈ keys
  · obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    have split := List.nodup_append.mp distinctKeys
    have afterSplit := List.nodup_cons.mp split.2.1
    have restDistinct : (before ++ after).Nodup :=
      List.nodup_append.mpr ⟨split.1, afterSplit.2, fun first inBefore second inAfter =>
        split.2.2 first inBefore second (List.Mem.tail _ inAfter)⟩
    have widen : ∀ other ∈ before ++ after, other ∈ before ++ key :: after := by
      intro other inside
      rcases List.mem_append.mp inside with inBefore | inAfter
      · exact List.mem_append_left _ inBefore
      · exact List.mem_append_right _ (List.Mem.tail _ inAfter)
    have fresh : ∀ other ∈ before ++ after, other ≠ key := by
      intro other inside
      rcases List.mem_append.mp inside with inBefore | inAfter
      · exact split.2.2 other inBefore key (List.Mem.head _)
      · exact fun same => afterSplit.1 (same ▸ inAfter)
    have restMeasurable : ∀ other ∈ before ++ after, space.Measurable (sets other) :=
      fun other inside => measurable other (widen other inside)
    have keyMeasurable := measurable key (List.mem_append_right _ (List.Mem.head _))
    have equal : Set.preimage (fun pair : α × (ι → α) => replace pair.2 key pair.1)
        (cylinder (before ++ key :: after) sets) =
          Set.product (sets key) (cylinder (before ++ after) sets) := by
      apply Set.ext
      intro pair
      constructor
      · intro inside
        refine ⟨?_, fun other inRest => ?_⟩
        · have atKey := inside key (List.mem_append_right _ (List.Mem.head _))
          change sets key (replace pair.2 key pair.1 key) at atKey
          rwa [replace_same] at atKey
        · have atOther := inside other (widen other inRest)
          change sets other (replace pair.2 key pair.1 other) at atOther
          rwa [replace_other _ _ (fresh other inRest)] at atOther
      · rintro ⟨atKey, rest⟩ other inside
        change sets other (replace pair.2 key pair.1 other)
        by_cases same : other = key
        · rw [same, replace_same]
          exact atKey
        · rw [replace_other _ _ same]
          refine rest other ?_
          rcases List.mem_append.mp inside with inBefore | inAfter
          · exact List.mem_append_left _ inBefore
          · cases inAfter with
            | head => exact absurd rfl same
            | tail _ inAfter => exact List.mem_append_right _ inAfter
    rw [equal, Measure.prod_apply_product _ _ _ keyMeasurable (cylinder_measurable restMeasurable),
      product _ restDistinct sets restMeasurable, massProduct_middle]
    rw [show replace laws key law key = law from replace_same laws key law]
    exact congrArg (ENNReal.mul _) (massProduct_congr fun other inside =>
      congrArg (fun law : Measure space => law (sets other))
        (replace_other laws law (fresh other inside)).symm)
  · have away : ∀ other ∈ keys, other ≠ key := fun other inKeys same => member (same ▸ inKeys)
    have equal : Set.preimage (fun pair : α × (ι → α) => replace pair.2 key pair.1)
        (cylinder keys sets) = Set.product Set.univ (cylinder keys sets) := by
      apply Set.ext
      intro pair
      constructor
      · intro inside
        refine ⟨True.intro, fun other inKeys => ?_⟩
        have atOther := inside other inKeys
        change sets other (replace pair.2 key pair.1 other) at atOther
        rwa [replace_other _ _ (away other inKeys)] at atOther
      · rintro ⟨_, rest⟩ other inKeys
        change sets other (replace pair.2 key pair.1 other)
        rw [replace_other _ _ (away other inKeys)]
        exact rest other inKeys
    rw [equal, Measure.prod_apply_product _ _ _ space.univ (cylinder_measurable measurable),
      product keys distinctKeys sets measurable, lawProbability.univ_eq_one, ENNReal.one_mul]
    exact massProduct_congr fun other inside =>
      congrArg (fun law : Measure space => law (sets other))
        (replace_other laws law (away other inside)).symm

/-- Prepending one independent coordinate to a product over `Fin n` gives a
product over `Fin (n + 1)`, whose first law is the new coordinate's. -/
theorem cons {n : Nat} {measure : Measure (Space.pi fun _ : Fin n => space)}
    {laws : Fin n → Measure space} (product : IsProduct measure laws) (head : Measure space)
    (headProbability : head.IsProbability) (finite : Measure.SFinite measure)
    (measurable : MeasurableMap (Space.product space (Space.pi fun _ : Fin n => space))
      (Space.pi fun _ : Fin (n + 1) => space) (fun pair => Fin.cases pair.1 pair.2)) :
    IsProduct ((Measure.prod head measure finite).map (fun pair => Fin.cases pair.1 pair.2)
        measurable) (Fin.cases head laws) := by
  intro keys distinctKeys sets setsMeasurable
  rw [Measure.map_apply _ _ _ (cylinder_measurable setsMeasurable)]
  have tailMeasurable : ∀ position ∈ tails keys, space.Measurable (sets position.succ) :=
    fun position member => setsMeasurable _ (mem_tails.mp member)
  have tailCylinder : ∀ pair : α × (Fin n → α),
      (∀ key ∈ keys, sets key (Fin.cases pair.1 pair.2 key)) ↔
        ((0 : Fin (n + 1)) ∈ keys → sets 0 pair.1) ∧
          cylinder (tails keys) (fun position => sets position.succ) pair.2 := by
    intro pair
    constructor
    · intro inside
      refine ⟨fun member => ?_, fun position member => ?_⟩
      · have atZero := inside 0 member
        simpa using atZero
      · have atSucc := inside _ (mem_tails.mp member)
        simpa using atSucc
    · rintro ⟨atZero, rest⟩ key member
      induction key using Fin.cases with
      | zero => simpa using atZero member
      | succ position => simpa using rest position (mem_tails.mpr member)
  by_cases zero : (0 : Fin (n + 1)) ∈ keys
  · obtain ⟨before, after, rfl⟩ := List.append_of_mem zero
    have split := List.nodup_append.mp distinctKeys
    have afterSplit := List.nodup_cons.mp split.2.1
    have restMissing : (0 : Fin (n + 1)) ∉ before ++ after := by
      intro inside
      rcases List.mem_append.mp inside with inBefore | inAfter
      · exact split.2.2 0 inBefore 0 (List.Mem.head _) rfl
      · exact afterSplit.1 inAfter
    have equal : Set.preimage (fun pair : α × (Fin n → α) => Fin.cases pair.1 pair.2)
        (cylinder (before ++ 0 :: after) sets) =
          Set.product (sets 0) (cylinder (tails (before ++ 0 :: after))
            (fun position => sets position.succ)) := by
      apply Set.ext
      intro pair
      refine (tailCylinder pair).trans ⟨fun inside => ⟨inside.1 ?_, inside.2⟩,
        fun inside => ⟨fun _ => inside.1, inside.2⟩⟩
      exact List.mem_append_right _ (List.Mem.head _)
    rw [equal, Measure.prod_apply_product _ _ _
        (setsMeasurable 0 (List.mem_append_right _ (List.Mem.head _)))
        (cylinder_measurable tailMeasurable),
      product _ (tails_nodup distinctKeys) _ tailMeasurable, massProduct_middle,
      ← map_succ_tails (before ++ after) restMissing, massProduct_map, tails_append_zero]
    rfl
  · have equal : Set.preimage (fun pair : α × (Fin n → α) => Fin.cases pair.1 pair.2)
        (cylinder keys sets) =
          Set.product Set.univ (cylinder (tails keys) (fun position => sets position.succ)) := by
      apply Set.ext
      intro pair
      refine (tailCylinder pair).trans ⟨fun inside => ⟨True.intro, inside.2⟩,
        fun inside => ⟨fun member => absurd member zero, inside.2⟩⟩
    rw [equal, Measure.prod_apply_product _ _ _ space.univ (cylinder_measurable tailMeasurable),
      product _ (tails_nodup distinctKeys) _ tailMeasurable, headProbability.univ_eq_one,
      ENNReal.one_mul]
    conv => rhs; rw [← map_succ_tails keys zero]
    rw [massProduct_map]
    rfl

end IsProduct

end

end Problib.Measure.Pi
