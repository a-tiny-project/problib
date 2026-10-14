module
public import Problib.Measure.Configuration.Reference
public import Problib.Measure.Configuration.Shuffle
public import Problib.Measure.StandardBorel.Basic
public import Problib.Measure.Real.Order

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real
public section
universe u
variable {α : Type u}

/-- Product of multiplicity factorials, accumulated along the list. -/
@[expose] public def stabilizerCount [BEq α] : List α → Nat
  | [] => 1
  | value :: values => (value :: values).count value * stabilizerCount values

public theorem stabilizerCount_perm [BEq α] [LawfulBEq α]
    {left right : List α} (permutation : left.Perm right) :
    stabilizerCount left = stabilizerCount right := by
  induction permutation with
  | nil => rfl
  | cons value permutation induction =>
      simp only [stabilizerCount, List.count_cons_self, induction,
        permutation.count_eq value]
  | swap first second rest =>
      by_cases equal : first = second
      · subst second
        rfl
      · simp [stabilizerCount, List.count_cons_self,
          List.count_cons_of_ne equal,
          List.count_cons_of_ne (Ne.symm equal),
          Nat.mul_left_comm]
  | trans before after beforeEqual afterEqual =>
      exact beforeEqual.trans afterEqual

example : stabilizerCount [false, false] = 2 := by decide
example : stabilizerCount [false, true] = 1 := by decide

/-- A natural number as an extended nonnegative real. -/
@[expose] public noncomputable def ennrealOfNat (count : Nat) : ENNReal :=
  ENNReal.ofRat (count : Rat) (by exact_mod_cast Nat.zero_le count)

public theorem ennrealOfNat_zero : ennrealOfNat 0 = ENNReal.zero := by
  unfold ennrealOfNat
  rw [← ENNReal.ofRat_zero]
  rfl

public theorem ennrealOfNat_one : ennrealOfNat 1 = ENNReal.one := by
  unfold ennrealOfNat
  rw [← ENNReal.ofRat_one]
  rfl

public theorem ennrealOfNat_add (left right : Nat) :
    ennrealOfNat (left + right) =
      ENNReal.add (ennrealOfNat left) (ennrealOfNat right) := by
  unfold ennrealOfNat
  rw [← ENNReal.ofRat_add]
  congr 1
  push_cast
  rfl

public theorem ennrealOfNat_mul (left right : Nat) :
    ennrealOfNat (left * right) =
      ENNReal.mul (ennrealOfNat left) (ennrealOfNat right) := by
  unfold ennrealOfNat
  rw [← ENNReal.ofRat_mul]
  congr 1
  push_cast
  rfl

/-- Summing a mass over the positions that hold a value counts the value. -/
public theorem partialSum_count [DecidableEq α] (values : List α) (value : α)
    (mass : ENNReal) :
    ENNReal.partialSum (fun index =>
        if values[index]? = some value then mass else ENNReal.zero) values.length =
      ENNReal.mul (ennrealOfNat (values.count value)) mass := by
  induction values with
  | nil =>
      rw [List.count_nil, ennrealOfNat_zero, ENNReal.zero_mul]
      rfl
  | cons head tail induction =>
      have shifted : (fun index => if (head :: tail)[1 + index]? = some value
          then mass else ENNReal.zero) =
          (fun index => if tail[index]? = some value then mass else ENNReal.zero) := by
        funext index
        rw [Nat.add_comm, List.getElem?_cons_succ]
      rw [List.length_cons, Nat.add_comm, ENNReal.partialSum_append, shifted,
        induction, List.count_cons, ennrealOfNat_add]
      change ENNReal.add (ENNReal.add ENNReal.zero
          (if some head = some value then mass else ENNReal.zero)) _ = _
      rw [ENNReal.zero_add]
      by_cases equal : head = value
      · rw [ite_eq_left (show some head = some value by rw [equal]),
          ite_eq_left (beq_iff_eq.mpr equal), ennrealOfNat_one,
          ENNReal.mul_comm (ENNReal.add _ _) mass, ENNReal.mul_add, ENNReal.mul_one,
          ENNReal.add_comm, ENNReal.mul_comm mass]
      · rw [ite_eq_right (fun same => equal (Option.some.inj same)),
          ite_eq_right (fun same => equal (beq_iff_eq.mp same)), ennrealOfNat_zero,
          ENNReal.add_zero, ENNReal.zero_add]

/-- The uniform weight times the bound is one. -/
public theorem uniformWeight_mul_ennrealOfNat {bound : Nat} (positive : 0 < bound) :
    ENNReal.mul (Measure.uniformWeight bound) (ennrealOfNat bound) = ENNReal.one :=
  Measure.uniformWeight_mul_bound positive

/-- Every singleton of a list space with measurable singletons is
measurable. -/
public theorem list_singleton_measurable {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value)) :
    ∀ values : List α, (Space.list element).Measurable (Set.singleton values)
  | [] => by
      have equal : Set.singleton ([] : List α) =
          Set.preimage List.length (Set.singleton 0) := by
        funext values
        apply propext
        exact ⟨(fun equal => by rw [equal]; rfl),
          (fun length => List.eq_nil_of_length_eq_zero length)⟩
      rw [equal]
      exact ListSpace.length_measurable element trivial
  | value :: values => by
      have equal : Set.singleton (value :: values) =
          Set.preimage ListSpace.view (Set.singleton (Sum.inr (value, values))) := by
        funext candidate
        apply propext
        cases candidate with
        | nil =>
            exact ⟨(fun impossible => by cases impossible),
              (fun impossible => by cases impossible)⟩
        | cons head tail =>
            exact ⟨(fun same => by rw [same]; rfl), (fun same => by cases same; rfl)⟩
      have product : Set.preimage Sum.inr
          (Set.singleton (Sum.inr (value, values) : Sum Unit (α × List α))) =
          Set.product (Set.singleton value) (Set.singleton values) := by
        funext pair
        apply propext
        constructor
        · intro same
          cases same
          exact ⟨rfl, rfl⟩
        · intro member
          exact congrArg Sum.inr (Prod.ext member.1 member.2)
      rw [equal]
      apply ListSpace.view_measurable element
      refine (Space.sum_measurable_iff _ _ _).mpr ⟨trivial, ?_⟩
      rw [product]
      exact Space.product_set_measurable _ _ (singletons value)
        (list_singleton_measurable singletons values)

/-- Finite sets of lists are measurable when singletons are. -/
public theorem list_membership_measurable {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value)) :
    ∀ points : List (List α),
      (Space.list element).Measurable (fun values => values ∈ points)
  | [] => by
      have empty : (fun values : List α => values ∈ ([] : List (List α))) =
          Set.empty :=
        funext fun _ => propext ⟨(fun member => nomatch member), (fun impossible => False.elim impossible)⟩
      rw [empty]
      exact (Space.list element).empty
  | point :: points => by
      have union : (fun values : List α => values ∈ point :: points) =
          Set.union (Set.singleton point) (fun values => values ∈ points) :=
        funext fun _ => propext List.mem_cons
      rw [union]
      exact (Space.list element).union (list_singleton_measurable singletons point)
        (list_membership_measurable singletons points)

/-- Every code for lists of a length, each entry at most its index. -/
@[expose] public def allCodes : Nat → List (List Nat)
  | 0 => [[]]
  | count + 1 => (List.range (count + 1)).flatMap
      (fun position => (allCodes count).map (fun code => position :: code))

private theorem eraseIdx_perm {other values : List α} {value : α} {position : Nat}
    (permutation : other.Perm (value :: values)) (below : position < other.length)
    (element : other[position] = value) :
    (other.eraseIdx position).Perm values := by
  have restored : (other.eraseIdx position).insertIdx position value = other := by
    rw [← element]
    exact insertIdx_eraseIdx_self below
  have lengthErased : position ≤ (other.eraseIdx position).length := by
    rw [List.length_eraseIdx_of_lt below]
    omega
  have toCons := List.perm_insertIdx value (other.eraseIdx position) lengthErased
  rw [restored] at toCons
  exact (List.perm_cons value).mp (toCons.symm.trans permutation)

/-- Every reordering of a list is reached by one of its codes. -/
public theorem perm_exists_code :
    ∀ {values other : List α}, other.Perm values →
      ∃ code ∈ allCodes values.length, applyCode code values = other
  | [], other, permutation => by
      rw [List.perm_nil.mp permutation]
      exact ⟨[], List.mem_singleton.mpr rfl, rfl⟩
  | value :: values, other, permutation => by
      have member : value ∈ other :=
        permutation.symm.mem_iff.mp List.mem_cons_self
      obtain ⟨position, below, element⟩ := List.mem_iff_getElem.mp member
      obtain ⟨code, codeMember, applied⟩ :=
        perm_exists_code (eraseIdx_perm permutation below element)
      have lengthEqual : other.length = values.length + 1 := permutation.length_eq
      refine ⟨position :: code, ?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨position, List.mem_range.mpr (by omega),
          List.mem_map.mpr ⟨code, codeMember, rfl⟩⟩
      · change (applyCode code values).insertIdx
          (min position (applyCode code values).length) value = other
        rw [applyCode_length, Nat.min_eq_left (by omega), applied, ← element]
        exact insertIdx_eraseIdx_self below

/-- The orderings of a list form a measurable set when singletons are
measurable. -/
public theorem orbit_measurable {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    (values : List α) :
    (Space.list element).Measurable (fun other => other.Perm values) := by
  have equal : (fun other : List α => other.Perm values) =
      (fun other => other ∈ (allCodes values.length).map
        (fun code => applyCode code values)) := by
    funext other
    apply propext
    constructor
    · intro permutation
      obtain ⟨code, member, applied⟩ := perm_exists_code permutation
      exact List.mem_map.mpr ⟨code, member, applied⟩
    · intro member
      obtain ⟨code, _, applied⟩ := List.mem_map.mp member
      rw [← applied]
      exact applyCode_perm code values
  rw [equal]
  exact list_membership_measurable singletons _

/-- The labelled lists over one configuration are its orderings. -/
public theorem unorder_preimage_singleton (values : List α) :
    Set.preimage unorder (Set.singleton (unorder values)) =
      (fun other : List α => other.Perm values) :=
  funext fun _ => propext ⟨Quotient.exact,
    fun related => show unorder _ = unorder values from Quotient.sound related⟩

/-- Each configuration is a measurable point of the unordered space when
singletons are measurable. -/
public theorem unorder_singleton_measurable {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    (values : List α) :
    (Space.unordered element).Measurable (Set.singleton (unorder values)) := by
  change (Space.list element).Measurable
    (Set.preimage unorder (Set.singleton (unorder values)))
  rw [unorder_preimage_singleton]
  exact orbit_measurable singletons values

private theorem insertIdx_eq_iff {values other : List α} {position : Nat}
    {value : α} (length : other.length = values.length + 1)
    (below : position ≤ values.length) :
    values.insertIdx position value = other ↔
      other[position]? = some value ∧ values = other.eraseIdx position := by
  constructor
  · intro equal
    subst equal
    refine ⟨?_, (List.eraseIdx_insertIdx_self value).symm⟩
    rw [List.getElem?_insertIdx_self, ite_eq_left below]
  · rintro ⟨atPosition, rfl⟩
    obtain ⟨positionBelow, element⟩ := List.getElem?_eq_some_iff.mp atPosition
    rw [← element]
    exact insertIdx_eraseIdx_self positionBelow

/-- The mass of one ordering of `value :: values` sums the tail's masses over
the positions that hold `value`. -/
public theorem shuffle_cons_singleton [DecidableEq α] {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    (value : α) (values other : List α) (length : other.length = values.length + 1) :
    shuffle element (value :: values) (Set.singleton other) =
      ENNReal.mul (Measure.uniformWeight (values.length + 1))
        (ENNReal.partialSum (fun position =>
          if other[position]? = some value then
            shuffle element values (Set.singleton (other.eraseIdx position))
          else ENNReal.zero) (values.length + 1)) := by
  have otherMeasurable := list_singleton_measurable singletons other
  have codesMeasurable := positions_map_measurable (Space.list element)
    (fun code => applyCode code (value :: values)) otherMeasurable
  rw [shuffle_apply, Measure.map_apply _ _ _ otherMeasurable]
  change Measure.codeLaw (values.length + 1) _ = _
  rw [Measure.codeLaw_succ, Measure.map_apply _ _ _ codesMeasurable,
    ← Measure.prod_swap (Measure.uniformBelowSFinite (values.length + 1))
      (Measure.SFinite.codeLaw values.length),
    Measure.map_apply _ _ _ (cons_code_measurable codesMeasurable),
    Measure.prod_apply _ _ _ (Space.swap_measurable _ _
      (cons_code_measurable codesMeasurable)),
    Measure.uniformBelow_lintegral_congr (right := fun position =>
      if other[position]? = some value then
        shuffle element values (Set.singleton (other.eraseIdx position))
      else ENNReal.zero),
    Measure.uniformBelow_lintegral]
  intro position below
  change Measure.codeLaw values.length (fun code => (applyCode code values).insertIdx
    (min position (applyCode code values).length) value = other) = _
  have sameSet : (fun code => (applyCode code values).insertIdx
      (min position (applyCode code values).length) value = other) =
      (fun code => other[position]? = some value ∧
        applyCode code values = other.eraseIdx position) := by
    funext code
    rw [applyCode_length, Nat.min_eq_left (Nat.le_of_lt_succ below)]
    exact propext (insertIdx_eq_iff (by rw [applyCode_length]; exact length)
      (by rw [applyCode_length]; exact Nat.le_of_lt_succ below))
  rw [sameSet]
  by_cases atPosition : other[position]? = some value
  · rw [ite_eq_left atPosition, shuffle_apply,
      Measure.map_apply _ _ _ (list_singleton_measurable singletons _)]
    have fiber : (fun code => other[position]? = some value ∧
        applyCode code values = other.eraseIdx position) =
        Set.preimage (fun code => applyCode code values)
          (Set.singleton (other.eraseIdx position)) :=
      funext fun _ => propext ⟨fun both => both.2, fun same => ⟨atPosition, same⟩⟩
    rw [fiber]
  · rw [ite_eq_right atPosition]
    have empty : (fun code => other[position]? = some value ∧
        applyCode code values = other.eraseIdx position) = Set.empty :=
      funext fun _ => propext ⟨fun both => atPosition both.1, fun impossible => impossible.elim⟩
    rw [empty]
    exact (Measure.codeLaw values.length).empty_apply

/-- The atoms of the random ordering: `n! · shuffle(x){x'} = |Stab x|` whenever
`x'` reorders `x`. -/
public theorem factorial_mul_shuffle_apply [DecidableEq α] {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value)) :
    ∀ {values other : List α}, other.Perm values →
      ENNReal.mul (ennrealOfNat (factorial values.length))
          (shuffle element values (Set.singleton other)) =
        ennrealOfNat (stabilizerCount values)
  | [], other, permutation => by
      rw [List.perm_nil.mp permutation, shuffle_nil,
        Measure.dirac_apply _ _ (list_singleton_measurable singletons []),
        ite_eq_left (show Set.singleton ([] : List α) [] from rfl), ENNReal.mul_one]
      rfl
  | value :: values, other, permutation => by
      have length : other.length = values.length + 1 := permutation.length_eq
      rw [shuffle_cons_singleton singletons value values other length]
      change ENNReal.mul (ennrealOfNat ((values.length + 1) * factorial values.length)) _ = _
      rw [ennrealOfNat_mul]
      let weight := Measure.uniformWeight (values.length + 1)
      let bound := ennrealOfNat (values.length + 1)
      let factor := ennrealOfNat (factorial values.length)
      let terms := fun position => if other[position]? = some value then
        shuffle element values (Set.singleton (other.eraseIdx position))
        else ENNReal.zero
      calc ENNReal.mul (ENNReal.mul bound factor)
            (ENNReal.mul weight (ENNReal.partialSum terms (values.length + 1)))
          = ENNReal.mul (ENNReal.mul weight bound)
              (ENNReal.mul factor (ENNReal.partialSum terms (values.length + 1))) := by
            rw [ENNReal.mul_assoc bound factor, ← ENNReal.mul_assoc factor weight,
              ENNReal.mul_comm factor weight, ENNReal.mul_assoc weight factor,
              ← ENNReal.mul_assoc bound weight, ENNReal.mul_comm bound weight]
        _ = ENNReal.mul factor (ENNReal.partialSum terms (values.length + 1)) := by
            rw [uniformWeight_mul_ennrealOfNat (Nat.succ_pos _), ENNReal.one_mul]
        _ = ENNReal.partialSum (fun position => ENNReal.mul factor (terms position))
              (values.length + 1) := (ENNReal.partialSum_mul_left _ _ _).symm
        _ = ENNReal.partialSum (fun position => if other[position]? = some value then
              ennrealOfNat (stabilizerCount values) else ENNReal.zero)
              (values.length + 1) := by
            apply ENNReal.partialSum_congr
            intro position
            by_cases atPosition : other[position]? = some value
            · obtain ⟨below, element⟩ := List.getElem?_eq_some_iff.mp atPosition
              simp only [terms, ite_eq_left atPosition]
              exact factorial_mul_shuffle_apply singletons
                (eraseIdx_perm permutation below element)
            · simp only [terms, ite_eq_right atPosition]
              exact ENNReal.mul_zero _
        _ = ENNReal.mul (ennrealOfNat (other.count value))
              (ennrealOfNat (stabilizerCount values)) := by
            rw [← length]
            exact partialSum_count other value _
        _ = ennrealOfNat (stabilizerCount (value :: values)) := by
            rw [← ennrealOfNat_mul, permutation.count_eq value]
            rfl

private theorem shuffle_singleton_of_not_perm {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    {values other : List α} (unrelated : ¬ other.Perm values) :
    shuffle element values (Set.singleton other) = ENNReal.zero := by
  rw [shuffle_apply, Measure.map_apply _ _ _ (list_singleton_measurable singletons other)]
  have empty : Set.preimage (fun code => applyCode code values) (Set.singleton other) =
      Set.empty :=
    funext fun code => propext ⟨fun same => unrelated (same ▸ applyCode_perm code values),
      fun impossible => impossible.elim⟩
  rw [empty]
  exact (Measure.codeLaw values.length).empty_apply

/-- Orbit mass times stabilizer equals `n!` times atom mass for an exchangeable
law. -/
public theorem exchangeable_orbit_mass [DecidableEq α] {element : Space α}
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    {law : Measure (Space.list element)} (exchangeable : Exchangeable law)
    (values : List α) :
    ENNReal.mul (ennrealOfNat (stabilizerCount values))
        ((law.map unorder (unorder_quotient_map element).measurable)
          (Set.singleton (unorder values))) =
      ENNReal.mul (ennrealOfNat (factorial values.length))
        (law (Set.singleton values)) := by
  have orbitMeasurable := orbit_measurable singletons values
  have orbitSet := unorder_preimage_singleton values
  have classMeasurable := unorder_singleton_measurable singletons values
  have singletonMeasurable := list_singleton_measurable singletons values
  have exchanged : law.bind (shuffle element) = law := exchangeable
  rw [Measure.map_apply _ _ _ classMeasurable, orbitSet]
  conv => rhs; rw [← exchanged]
  rw [Measure.bind_apply _ _ singletonMeasurable,
    ← lintegral_smul _ _ ((shuffle element).measurable singletonMeasurable),
    Measure.apply_eq_lintegral_indicator law orbitMeasurable,
    ← lintegral_smul _ _ (ENNRealMeasurable.indicator orbitMeasurable
      (ENNRealMeasurable.constant _ ENNReal.one))]
  apply lintegral_congr
  intro other
  unfold ennrealIndicator ennrealPiecewise
  by_cases related : other.Perm values
  · rw [ite_eq_left related, ENNReal.mul_one, ← related.length_eq,
      factorial_mul_shuffle_apply singletons related.symm,
      stabilizerCount_perm related]
  · rw [ite_eq_right related, ENNReal.mul_zero,
      shuffle_singleton_of_not_perm singletons (fun reverse => related reverse.symm),
      ENNReal.mul_zero]

/-- A list power whose reference has unit atoms gives every list of the
power's length unit mass. -/
public theorem listPower_singleton_unit {element : Space α}
    (reference : Measure element) (finite : Measure.SFinite reference)
    (singletons : ∀ value, element.Measurable (Set.singleton value))
    (unit : ∀ value, reference (Set.singleton value) = ENNReal.one) :
    ∀ values : List α,
      Measure.listPower reference finite values.length (Set.singleton values) =
        ENNReal.one
  | [] => by
      change Measure.listPower reference finite 0 _ = _
      rw [Measure.listPower_zero,
        Measure.dirac_apply _ _ (list_singleton_measurable singletons []),
        ite_eq_left (show Set.singleton ([] : List α) [] from rfl)]
  | value :: values => by
      have product : Set.preimage (fun input : α × List α => input.1 :: input.2)
          (Set.singleton (value :: values)) =
          Set.product (Set.singleton value) (Set.singleton values) := by
        funext pair
        apply propext
        constructor
        · intro same
          exact List.cons.inj same
        · intro member
          show pair.1 :: pair.2 = value :: values
          rw [member.1, member.2]
      change Measure.listPower reference finite (values.length + 1) _ = _
      rw [Measure.listPower_succ,
        Measure.map_apply _ _ _ (list_singleton_measurable singletons _), product,
        Measure.prod_apply_product _ _ _ (singletons value)
          (list_singleton_measurable singletons values),
        unit, listPower_singleton_unit reference finite singletons unit values,
        ENNReal.one_mul]

/-- Unit mass at every point of a countably coded type. -/
@[expose] public noncomputable def unitCounting (code : α → Nat) :
    Measure (Space.discrete α) := by
  classical
  exact Measure.sum (fun index =>
    if found : ∃ value, code value = index then
      Measure.dirac (Space.discrete α) (Classical.choose found)
    else Measure.zero _)

public noncomputable def unitCountingSFinite (code : α → Nat) :
    Measure.SFinite (unitCounting code) := by
  classical
  let components : Nat → Measure (Space.discrete α) := fun index =>
    if found : ∃ value, code value = index then
      Measure.dirac (Space.discrete α) (Classical.choose found)
    else Measure.zero _
  have finite : ∀ index, Measure.SFinite (components index) := by
    intro index
    dsimp only [components]
    split
    · exact Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)
    · exact Measure.SFinite.zero _
  exact Measure.SFinite.sum components finite

/-- An injective code gives every point unit mass. -/
public theorem unitCounting_singleton {code : α → Nat}
    (injective : Function.Injective code) (value : α) :
    unitCounting code (Set.singleton value) = ENNReal.one := by
  classical
  unfold unitCounting
  rw [Measure.sum_apply _ trivial,
    ENNReal.tsum_eq_of_at_most_one_nonzero _ (code value)]
  · have found : ∃ candidate, code candidate = code value := ⟨value, rfl⟩
    rw [dite_eq_left found]
    have chosen : Classical.choose found = value :=
      injective (Classical.choose_spec found)
    rw [chosen]
    exact Measure.dirac_apply_of_mem _ _ trivial rfl
  · intro index different
    by_cases found : ∃ candidate, code candidate = index
    · rw [dite_eq_left found]
      apply Measure.dirac_apply_of_not_mem _ _ trivial
      intro same
      apply different
      rw [← Classical.choose_spec found]
      exact congrArg code same
    · rw [dite_eq_right found]
      exact Measure.zero_apply _

/-- The number of distinct orderings of a list, as the mass that unit
counting per ordering gives its orbit. -/
@[expose] public noncomputable def orbitCount (code : α → Nat) (values : List α) :
    ENNReal :=
  ((Measure.listPower (unitCounting code) (unitCountingSFinite code)
      values.length).map unorder
    (unorder_quotient_map (Space.discrete α)).measurable)
    (Set.singleton (unorder values))

/-- Distinct orderings times stabilizer size is `n!`. -/
public theorem orbitCount_mul_stabilizer [DecidableEq α] {code : α → Nat}
    (injective : Function.Injective code) (values : List α) :
    ENNReal.mul (ennrealOfNat (stabilizerCount values)) (orbitCount code values) =
      ennrealOfNat (factorial values.length) := by
  have mass := exchangeable_orbit_mass (element := Space.discrete α)
    (fun _ => trivial)
    (listPower_exchangeable (unitCounting code) (unitCountingSFinite code)
      values.length) values
  rw [listPower_singleton_unit _ _ (fun _ => trivial)
    (unitCounting_singleton injective) values, ENNReal.mul_one] at mass
  exact mass

private theorem mem_iff_coordinate (value : α) :
    ∀ values : List α,
      value ∈ values ↔ ∃ index, ListSpace.coordinate index values = Sum.inr value
  | [] => by
      constructor
      · intro member
        exact nomatch member
      · rintro ⟨index, found⟩
        cases index <;> exact nomatch found
  | head :: tail => by
      constructor
      · intro member
        rcases List.mem_cons.mp member with same | later
        · exact ⟨0, by rw [same]; rfl⟩
        · obtain ⟨index, found⟩ := (mem_iff_coordinate value tail).mp later
          exact ⟨index + 1, found⟩
      · rintro ⟨index, found⟩
        cases index with
        | zero =>
            have same : head = value := Sum.inr.inj found
            rw [same]
            exact List.mem_cons_self
        | succ index =>
            exact List.mem_cons_of_mem head
              ((mem_iff_coordinate value tail).mpr ⟨index, found⟩)

/-- Membership of a point in a list is jointly measurable when the element
space is standard Borel. -/
private theorem membership_measurable {element : Space α}
    (presentation : StandardBorel element) :
    (Space.product element (Space.list element)).Measurable
      (fun pair : α × List α => pair.1 ∈ pair.2) := by
  let code := presentation.embeddingReal
  have presentMeasurable : (Space.sum (Space.discrete Unit) element).Measurable
      (fun slot : Sum Unit α => ∃ value, slot = Sum.inr value) := by
    refine (Space.sum_measurable_iff _ _ _).mpr ⟨trivial, ?_⟩
    have whole : Set.preimage Sum.inr
        (fun slot : Sum Unit α => ∃ value, slot = Sum.inr value) = Set.univ :=
      Set.ext fun value => ⟨fun _ => True.intro, fun _ => ⟨value, rfl⟩⟩
    rw [whole]
    exact element.univ
  have slotCode : MeasurableMap (Space.sum (Space.discrete Unit) element) Real.borel
      (Sum.elim (fun _ => Problib.Real.Construction.Dedekind.zero) code.function) :=
    MeasurableMap.sum_elim (MeasurableMap.constant _ _ _) code.measurable
  have piece : ∀ index, (Space.product element (Space.list element)).Measurable
      (fun pair : α × List α => ListSpace.coordinate index pair.2 = Sum.inr pair.1) := by
    intro index
    have slot : MeasurableMap (Space.product element (Space.list element))
        (Space.sum (Space.discrete Unit) element)
        (fun pair : α × List α => ListSpace.coordinate index pair.2) :=
      MeasurableMap.comp (ListSpace.coordinate_measurable element index)
        (Space.second_measurable _ _)
    have equal : (fun pair : α × List α =>
          ListSpace.coordinate index pair.2 = Sum.inr pair.1) =
        Set.inter
          (Set.preimage (fun pair : α × List α => ListSpace.coordinate index pair.2)
            (fun slot : Sum Unit α => ∃ value, slot = Sum.inr value))
          (fun pair : α × List α =>
            Sum.elim (fun _ => Problib.Real.Construction.Dedekind.zero) code.function
              (ListSpace.coordinate index pair.2) = code.function pair.1) := by
      apply Set.ext
      intro pair
      constructor
      · intro found
        refine ⟨⟨pair.1, found⟩, ?_⟩
        change Sum.elim (fun _ => Problib.Real.Construction.Dedekind.zero) code.function
          (ListSpace.coordinate index pair.2) = code.function pair.1
        rw [found]
        rfl
      · rintro ⟨⟨value, present⟩, coded⟩
        have found : ListSpace.coordinate index pair.2 = Sum.inr value := present
        change Sum.elim (fun _ => Problib.Real.Construction.Dedekind.zero) code.function
          (ListSpace.coordinate index pair.2) = code.function pair.1 at coded
        rw [found] at coded
        change ListSpace.coordinate index pair.2 = Sum.inr pair.1
        rw [found, code.injective coded]
    rw [equal]
    exact (Space.product element (Space.list element)).inter (slot presentMeasurable)
      (Real.measurable_eq (MeasurableMap.comp slotCode slot)
        (MeasurableMap.comp code.measurable (Space.first_measurable _ _)))
  have equal : (fun pair : α × List α => pair.1 ∈ pair.2) =
      Set.iUnion (fun index => fun pair : α × List α =>
        ListSpace.coordinate index pair.2 = Sum.inr pair.1) :=
    Set.ext fun pair => mem_iff_coordinate pair.1 pair.2
  rw [equal]
  exact (Space.product element (Space.list element)).iUnion piece

/-- Lists with a repeated entry form a measurable set when the element space
is standard Borel. -/
private theorem duplicate_measurable {element : Space α}
    (presentation : StandardBorel element) :
    (Space.list element).Measurable (fun values : List α => ¬ values.Nodup) := by
  have stratum : ∀ count, (Space.list element).Measurable
      (fun values : List α => values.length = count ∧ ¬ values.Nodup) := by
    intro count
    induction count with
    | zero =>
        have equal : (fun values : List α => values.length = 0 ∧ ¬ values.Nodup) =
            Set.empty := by
          apply Set.ext
          intro values
          constructor
          · rintro ⟨empty, repeated⟩
            rw [List.length_eq_zero_iff] at empty
            rw [empty] at repeated
            exact repeated List.nodup_nil
          · exact False.elim
        rw [equal]
        exact (Space.list element).empty
    | succ count induction =>
        let cases : Set (Sum Unit (α × List α)) := Sum.elim (fun _ => False)
          (fun pair => pair.2.length = count ∧ (pair.1 ∈ pair.2 ∨ ¬ pair.2.Nodup))
        have casesMeasurable : (Space.sum (Space.discrete Unit)
            (Space.product element (Space.list element))).Measurable cases := by
          refine (Space.sum_measurable_iff _ _ _).mpr ⟨trivial, ?_⟩
          have equal : Set.preimage Sum.inr cases =
              Set.inter
                (Set.preimage (fun pair : α × List α => pair.2.length)
                  (fun length => length = count))
                (Set.union (fun pair : α × List α => pair.1 ∈ pair.2)
                  (Set.preimage (fun pair : α × List α => pair.2)
                    (fun values => values.length = count ∧ ¬ values.Nodup))) := by
            apply Set.ext
            rintro ⟨head, tail⟩
            constructor
            · rintro ⟨length, member | repeated⟩
              · exact ⟨length, Or.inl member⟩
              · exact ⟨length, Or.inr ⟨length, repeated⟩⟩
            · rintro ⟨length, member | ⟨_, repeated⟩⟩
              · exact ⟨length, Or.inl member⟩
              · exact ⟨length, Or.inr repeated⟩
          rw [equal]
          exact (Space.product element (Space.list element)).inter
            (MeasurableMap.comp (ListSpace.length_measurable element)
              (Space.second_measurable _ _) trivial)
            ((Space.product element (Space.list element)).union
              (membership_measurable presentation)
              (Space.second_measurable _ _ induction))
        have equal : (fun values : List α => values.length = count + 1 ∧ ¬ values.Nodup) =
            Set.preimage ListSpace.view cases := by
          apply Set.ext
          intro values
          cases values with
          | nil =>
              constructor
              · rintro ⟨length, _⟩
                exact nomatch length
              · intro member
                exact nomatch member
          | cons head tail =>
              change (tail.length + 1 = count + 1 ∧ ¬ (head :: tail).Nodup) ↔
                (tail.length = count ∧ (head ∈ tail ∨ ¬ tail.Nodup))
              rw [List.nodup_cons, Nat.add_right_cancel_iff]
              constructor
              · rintro ⟨length, repeated⟩
                refine ⟨length, ?_⟩
                by_cases member : head ∈ tail
                · exact Or.inl member
                · exact Or.inr (fun distinct => repeated ⟨member, distinct⟩)
              · rintro ⟨length, member | repeated⟩
                · exact ⟨length, fun distinct => distinct.1 member⟩
                · exact ⟨length, fun distinct => repeated distinct.2⟩
        rw [equal]
        exact ListSpace.view_measurable element casesMeasurable
  have equal : (fun values : List α => ¬ values.Nodup) =
      Set.iUnion (fun count => fun values : List α =>
        values.length = count ∧ ¬ values.Nodup) :=
    Set.ext fun values =>
      ⟨fun repeated => ⟨values.length, rfl, repeated⟩, fun ⟨_, _, repeated⟩ => repeated⟩
  rw [equal]
  exact (Space.list element).iUnion stratum

/-- Under an atomless reference, a fixed point is almost surely absent from
every iid power. -/
private theorem listPower_member_null {element : Space α}
    (presentation : StandardBorel element) (reference : Measure element)
    (finite : Measure.SFinite reference)
    (atomless : ∀ value, reference (Set.singleton value) = ENNReal.zero)
    (value : α) (count : Nat) :
    Measure.listPower reference finite count (fun values => value ∈ values) =
      ENNReal.zero := by
  have memberMeasurable : (Space.list element).Measurable
      (fun values : List α => value ∈ values) :=
    Space.pair_measurable (MeasurableMap.constant _ _ value)
      (MeasurableMap.identity (Space.list element)) (membership_measurable presentation)
  induction count with
  | zero =>
      rw [Measure.listPower_zero, Measure.dirac_apply _ _ memberMeasurable]
      exact ite_eq_right List.not_mem_nil
  | succ count induction =>
      rw [Measure.listPower_succ, Measure.map_apply _ _ _ memberMeasurable,
        Measure.prod_apply _ _ _ (ListSpace.cons_measurable element memberMeasurable)]
      have vanishes : Measure.AEEq reference
          (fun head => Measure.listPower reference finite count
            (Set.preimage (fun tail => (head, tail))
              (Set.preimage (fun input : α × List α => input.1 :: input.2)
                (fun values => value ∈ values))))
          (fun _ => ENNReal.zero) := by
        apply Measure.NullSet.mono (atomless value)
        intro head differs
        change head = value
        apply Classical.byContradiction
        intro other
        apply differs
        have same : Set.preimage (fun tail => (head, tail))
            (Set.preimage (fun input : α × List α => input.1 :: input.2)
              (fun values => value ∈ values)) = (fun values => value ∈ values) := by
          apply Set.ext
          intro tail
          change value ∈ head :: tail ↔ value ∈ tail
          rw [List.mem_cons]
          exact ⟨fun found => found.resolve_left (fun equal => other equal.symm),
            Or.inr⟩
        change Measure.listPower reference finite count _ = ENNReal.zero
        rw [same]
        exact induction
      rw [lintegral_congr_ae vanishes, lintegral_zero]

/-- With an atomless reference, repeated entries are null in every iid
power, so the label stabilizer is trivial and the orbit factor is `n!`
almost everywhere. -/
public theorem diagonal_null_of_atomless {element : Space α}
    (presentation : StandardBorel element) (reference : Measure element)
    (finite : Measure.SFinite reference)
    (atomless : ∀ value, reference (Set.singleton value) = ENNReal.zero)
    (count : Nat) :
    Measure.listPower reference finite count (fun values => ¬ values.Nodup) =
      ENNReal.zero := by
  have repeatedMeasurable := duplicate_measurable presentation
  induction count with
  | zero =>
      rw [Measure.listPower_zero, Measure.dirac_apply _ _ repeatedMeasurable]
      exact ite_eq_right (fun repeated => repeated List.nodup_nil)
  | succ count induction =>
      rw [Measure.listPower_succ, Measure.map_apply _ _ _ repeatedMeasurable,
        Measure.prod_apply _ _ _ (ListSpace.cons_measurable element repeatedMeasurable)]
      have vanishes : ∀ head : α,
          Measure.listPower reference finite count
            (Set.preimage (fun tail => (head, tail))
              (Set.preimage (fun input : α × List α => input.1 :: input.2)
                (fun values => ¬ values.Nodup))) = ENNReal.zero := by
        intro head
        apply Measure.NullSet.mono
          (Measure.NullSet.union
            (listPower_member_null presentation reference finite atomless head count)
            induction)
        intro tail repeated
        change ¬ (head :: tail).Nodup at repeated
        rw [List.nodup_cons] at repeated
        by_cases member : head ∈ tail
        · exact Or.inl member
        · exact Or.inr (fun distinct => repeated ⟨member, distinct⟩)
      rw [lintegral_congr reference vanishes, lintegral_zero]

end
end Problib.Measure
