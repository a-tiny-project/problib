module

public import Problib.Measure.Kernel.Iteration.SmallSet
public import Problib.Measure.Kernel.Iteration.Irreducibility
public import Problib.Measure.Space.Generator
import Problib.Measure.Kernel.Hahn.Countable
import Problib.Measure.Approximation.Countable
import Problib.Measure.Space.Algebra
import Problib.Measure.Kernel.Product
import Problib.Measure.Kernel.Measurable.Section
import Problib.Measure.Additive.Restrict
import Problib.Measure.Normalization
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Zero
import Problib.Real.Approximation
import Problib.Real.Nonnegative.Embedding
import Problib.Real.Extended.Approximation
import Problib.Measure.Measurability

set_option autoImplicit false

/-!
# Small sets exist

A Markov kernel on a countably generated space that is irreducible against a
finite reference has a small set: a measurable region the reference charges, on
which one iterate dominates a scaled law that charges the region itself.

Hahn decompositions of each iterate against each scaled copy of the reference
give product-measurable rows on which the iterate dominates the scaled
reference. Irreducibility makes some row charged from every state. Composing a
charged row with a row that charges its columns, and approximating both by the
countable algebra, finds a pair of cells on which every composed row charges
the second cell by a fixed amount.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-! ### Scales -/

/-- A natural number as a nonnegative real. -/
private noncomputable def natural (count : Nat) : NNReal :=
  NNReal.ofRat (count : Rat) Rat.natCast_nonneg

/-- The scale `1 / (index + 1)`. -/
private noncomputable def scale (index : Nat) : NNReal :=
  NNReal.div NNReal.one (natural (index + 1))

private theorem scale_positive (index : Nat) :
    NNReal.lt NNReal.zero (scale index) := by
  apply NNReal.div_positive NNReal.one_positive
  have less := (NNReal.ofRat_lt_iff 0 ((index + 1 : Nat) : Rat) (by decide)
    Rat.natCast_nonneg).mpr (Rat.natCast_pos.mpr (Nat.succ_pos index))
  rw [NNReal.ofRat_zero] at less
  exact less

private theorem scale_small {bound : NNReal}
    (positive : NNReal.lt NNReal.zero bound) :
    ∃ index, NNReal.lt (scale index) bound := by
  rcases Construction.Dedekind.exists_positive_inverse_below positive with
    ⟨count, countPositive, below⟩
  have countLarge : 0 < count := by
    rcases Nat.eq_zero_or_pos count with vanished | large
    · subst vanished
      exfalso
      rw [show ((0 : Nat) : Rat) = 0 from rfl, Construction.Dedekind.ofRat_zero]
        at countPositive
      exact countPositive.right countPositive.left
    · exact large
  refine ⟨count - 1, ?_⟩
  have same : natural (count - 1 + 1) = natural count := by
    rw [Nat.sub_add_cancel countLarge]
  change Construction.Dedekind.lt
    (Construction.Dedekind.div (NNReal.toReal NNReal.one)
      (NNReal.toReal (natural (count - 1 + 1)))) (NNReal.toReal bound)
  rw [same, natural, NNReal.toReal_ofRat, NNReal.toReal_one,
    Construction.Dedekind.div_eq_mul_inverse, Construction.Dedekind.one_mul]
  exact below

/-! ### Sections -/

section Sections

variable {reference : Measure space}

/-- A relation read as a set of pairs. -/
private def pairs (relation : α → Set α) : Set (α × α) :=
  fun pair => relation pair.1 pair.2

/-- The states related to `second`. -/
private def column (relation : α → Set α) (second : α) : Set α :=
  fun first => relation first second

private theorem row_measurable {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation))
    (first : α) : space.Measurable (relation first) :=
  (Space.pair_measurable (MeasurableMap.constant space space first)
    (MeasurableMap.identity space)) measurable

private theorem column_measurable {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation))
    (second : α) : space.Measurable (column relation second) :=
  (Space.pair_measurable (MeasurableMap.identity space)
    (MeasurableMap.constant space space second)) measurable

private theorem section_measurable (finite : Measure.IsFinite reference)
    {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation)) :
    ENNRealMeasurable space (fun first => reference (relation first)) :=
  section_apply_measurable_of_finite_fibers (Kernel.const space reference)
    (fun _ => finite) measurable

/-- The pairs of a relation between two measurable sets. -/
private def between (relation : α → Set α) (rows columns : Set α) :
    Set (α × α) :=
  fun pair => rows pair.1 ∧ columns pair.2 ∧ relation pair.1 pair.2

private theorem between_measurable {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation))
    {rows columns : Set α} (rowsMeasurable : space.Measurable rows)
    (columnsMeasurable : space.Measurable columns) :
    (Space.product space space).Measurable (between relation rows columns) :=
  (Space.product space space).inter
    (Space.first_measurable space space rowsMeasurable)
    ((Space.product space space).inter
      (Space.second_measurable space space columnsMeasurable) measurable)

/-- Tonelli for a relation: integrating the related mass over rows equals
integrating the related mass over columns. -/
private theorem swap_section (finite : Measure.IsFinite reference)
    {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation))
    {rows columns : Set α} (rowsMeasurable : space.Measurable rows)
    (columnsMeasurable : space.Measurable columns) :
    lintegral reference (ennrealIndicator rows
        (fun first => reference (Set.inter columns (relation first)))) =
      lintegral reference (ennrealIndicator columns
        (fun second => reference (Set.inter rows (column relation second)))) := by
  let graph := between relation rows columns
  have graphMeasurable : (Space.product space space).Measurable graph :=
    between_measurable measurable rowsMeasurable columnsMeasurable
  let unit : α × α → ENNReal := ennrealIndicator graph (fun _ => ENNReal.one)
  have unitMeasurable : ENNRealMeasurable (Space.product space space) unit :=
    ENNRealMeasurable.indicator graphMeasurable (ENNRealMeasurable.constant _ _)
  let sfinite := Measure.SFinite.ofFinite finite
  have byRows := lintegral_prod reference reference sfinite unitMeasurable
  have byColumns := lintegral_prod_symm reference reference sfinite sfinite
    unitMeasurable
  have rowsInner : ∀ first, lintegral reference (fun second => unit (first, second)) =
      ennrealIndicator rows
        (fun first => reference (Set.inter columns (relation first))) first := by
    intro first
    by_cases inside : rows first
    · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left inside,
        apply_eq_lintegral_indicator reference
          (space.inter columnsMeasurable (row_measurable measurable first))]
      congr 1
      funext second
      by_cases related : Set.inter columns (relation first) second
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left related]
        exact ite_eq_left (show graph (first, second) from
          ⟨inside, related.1, related.2⟩)
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right related]
        exact ite_eq_right (fun member : graph (first, second) =>
          related ⟨member.2.1, member.2.2⟩)
    · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right inside]
      have vanish : (fun second => unit (first, second)) =
          (fun _ => ENNReal.zero) := by
        funext second
        exact ite_eq_right (fun member : graph (first, second) => inside member.1)
      rw [vanish, lintegral_const, ENNReal.zero_mul]
  have columnsInner : ∀ second,
      lintegral reference (fun first => unit (first, second)) =
        ennrealIndicator columns
          (fun second => reference (Set.inter rows (column relation second)))
          second := by
    intro second
    by_cases inside : columns second
    · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left inside,
        apply_eq_lintegral_indicator reference
          (space.inter rowsMeasurable (column_measurable measurable second))]
      congr 1
      funext first
      by_cases related : Set.inter rows (column relation second) first
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left related]
        exact ite_eq_left (show graph (first, second) from
          ⟨related.1, inside, related.2⟩)
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right related]
        exact ite_eq_right (fun member : graph (first, second) =>
          related ⟨member.1, member.2.2⟩)
    · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right inside]
      have vanish : (fun first => unit (first, second)) =
          (fun _ => ENNReal.zero) := by
        funext first
        exact ite_eq_right (fun member : graph (first, second) => inside member.2.1)
      rw [vanish, lintegral_const, ENNReal.zero_mul]
  rw [lintegral_congr reference rowsInner] at byRows
  rw [lintegral_congr reference columnsInner] at byColumns
  rw [← byRows, byColumns]

private theorem indicator_univ (function : α → ENNReal) :
    ennrealIndicator Set.univ function = function := by
  funext value
  exact ite_eq_left trivial

/-- The relation read backwards. -/
private def transpose (relation : α → Set α) : α → Set α :=
  fun second first => relation first second

private theorem transpose_measurable {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation)) :
    (Space.product space space).Measurable (pairs (transpose relation)) :=
  (Space.swap_measurable space space) measurable

private theorem column_section_measurable (finite : Measure.IsFinite reference)
    {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation)) :
    ENNRealMeasurable space (fun second => reference (column relation second)) :=
  section_measurable finite (transpose_measurable measurable)

/-- The mass where a row of one relation meets a column of another. -/
private noncomputable def meeting (reference : Measure space) (first second : α → Set α)
    (row last : α) : ENNReal :=
  reference (Set.inter (first row) (column second last))

private theorem meeting_measurable (finite : Measure.IsFinite reference)
    {first second : α → Set α}
    (firstMeasurable : (Space.product space space).Measurable (pairs first))
    (secondMeasurable : (Space.product space space).Measurable (pairs second)) :
    ENNRealMeasurable (Space.product space space)
      (fun pair => meeting reference first second pair.1 pair.2) := by
  let triple := Space.product (Space.product space space) space
  have left : MeasurableMap triple (Space.product space space)
      (fun value : (α × α) × α => (value.1.1, value.2)) := by
    measurability
  have right : MeasurableMap triple (Space.product space space)
      (fun value : (α × α) × α => (value.2, value.1.2)) := by
    measurability
  exact section_apply_measurable_of_finite_fibers
    (Kernel.const (Space.product space space) reference) (fun _ => finite)
    (triple.inter (left firstMeasurable) (right secondMeasurable))

/-- The meeting mass integrated over both ends. -/
private noncomputable def meetingMass (reference : Measure space)
    (first second : α → Set α) : ENNReal :=
  lintegral reference (fun row => lintegral reference (meeting reference first second row))

/-- Integrating a meeting over its far end integrates the second relation's
rows over one row of the first. -/
private theorem lintegral_meeting (finite : Measure.IsFinite reference)
    {first second : α → Set α}
    (firstMeasurable : (Space.product space space).Measurable (pairs first))
    (secondMeasurable : (Space.product space space).Measurable (pairs second))
    (row : α) :
    lintegral reference (meeting reference first second row) =
      lintegral reference
        (ennrealIndicator (first row) (fun middle => reference (second middle))) := by
  have swapped := swap_section finite secondMeasurable
    (row_measurable firstMeasurable row) space.univ
  simp only [Set.inter_univ_left, indicator_univ] at swapped
  exact swapped.symm

/-- Moving both sides of an intersection moves its mass by at most the two
distances. -/
private theorem inter_le_add (measure : Measure space)
    (left right nearLeft nearRight : Set α) :
    ENNReal.le (measure (Set.inter left right))
      (ENNReal.add (measure (Set.inter nearLeft nearRight))
        (ENNReal.add (measure.setDistance left nearLeft)
          (measure.setDistance right nearRight))) := by
  have covered : Set.Subset (Set.inter left right)
      (Set.union (Set.inter nearLeft nearRight)
        (Set.union (Set.symmDiff left nearLeft) (Set.symmDiff right nearRight))) := by
    intro value member
    by_cases inLeft : nearLeft value
    · by_cases inRight : nearRight value
      · exact Or.inl ⟨inLeft, inRight⟩
      · exact Or.inr (Or.inr (Or.inl ⟨member.2, inRight⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨member.1, inLeft⟩))
  exact ENNReal.le_trans (measure.mono covered)
    (ENNReal.le_trans (measure.union_le _ _)
      (ENNReal.add_le_add_left (measure.union_le _ _) _))

end Sections

/-! ### Rows -/

section Rows

variable {kernel : Kernel space space} {reference : Measure space}

/-- The states where `steps` iterations dominate the scaled reference. -/
private abbrev Dominance (kernel : Kernel space space) (reference : Measure space)
    (steps : Nat) (weight : NNReal) : Type u :=
  HahnDecomposition (iterate kernel steps)
    (Kernel.const space (Measure.smul (ENNReal.finite weight) reference))

private noncomputable def dominance (generator : Space.CountableGenerator space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (finite : Measure.IsFinite reference) (count index : Nat) :
    Dominance kernel reference (count + 1) (scale index) :=
  HahnDecomposition.ofCountableGenerator generator
    (fun input => (iterate_isProbability kernel markov (count + 1) input).to_finite)
    (fun _ => Measure.IsFinite.smul _ True.intro finite)

private theorem dominance_lower {steps : Nat} {weight : NNReal}
    (rows : Dominance kernel reference steps weight) (input : α)
    {event : Set α} (measurable : space.Measurable event) :
    ENNReal.le (ENNReal.mul (ENNReal.finite weight)
        (reference (Set.inter event (rows.region input))))
      (iterate kernel steps input event) := by
  have both := space.inter measurable (row_measurable rows.measurable input)
  have bound := rows.positive input both (fun _ member => member.2)
  rw [Kernel.const_apply, Measure.smul_apply_measurable _ _ both] at bound
  exact ENNReal.le_trans bound
    ((iterate kernel steps input).mono (fun _ member => member.1))

private theorem dominance_upper {steps : Nat} {weight : NNReal}
    (rows : Dominance kernel reference steps weight) (input : α)
    {event : Set α} (measurable : space.Measurable event)
    (outside : Set.Subset event (Set.complement (rows.region input))) :
    ENNReal.le (iterate kernel steps input event)
      (ENNReal.mul (ENNReal.finite weight) (reference event)) := by
  have bound := rows.negative input measurable outside
  rw [Kernel.const_apply, Measure.smul_apply_measurable _ _ measurable] at bound
  exact bound

/-- A null measurable set leaves the rest of a charged space charged. -/
private theorem complement_positive {region : Set α}
    (nonzero : ENNReal.lt ENNReal.zero (reference Set.univ))
    (null : reference.NullSet region) :
    ENNReal.lt ENNReal.zero (reference (Set.complement region)) := by
  have whole := reference.union_le region (Set.complement region)
  have covers : Set.union region (Set.complement region) = Set.univ := by
    funext value
    apply propext
    exact ⟨fun _ => trivial, fun _ => Classical.em (region value)⟩
  rw [covers, null, ENNReal.zero_add] at whole
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanished
  rw [vanished] at whole
  exact (ENNReal.zero_lt_iff_ne_zero.mp nonzero) (ENNReal.eq_zero_of_le_zero whole)

/-- Irreducibility makes some row charged from every state. -/
private theorem exists_charged_row (generator : Space.CountableGenerator space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (irreducible : MeasureIrreducible kernel reference)
    (finite : Measure.IsFinite reference) (input : α) :
    ∃ count index, ENNReal.lt ENNReal.zero
      (reference ((dominance generator markov finite count index).region input)) := by
  apply Classical.byContradiction
  intro none
  let covered : Set α := Set.iUnion fun count => Set.iUnion fun index =>
    (dominance generator markov finite count index).region input
  have coveredMeasurable : space.Measurable covered :=
    space.iUnion fun count => space.iUnion fun index =>
      row_measurable (dominance generator markov finite count index).measurable input
  have coveredNull : reference.NullSet covered :=
    Measure.NullSet.iUnion fun count => Measure.NullSet.iUnion fun index => by
      apply Classical.byContradiction
      intro charged
      exact none ⟨count, index, ENNReal.zero_lt_iff_ne_zero.mpr charged⟩
  have restPositive := complement_positive irreducible.nonzero coveredNull
  rcases irreducible.reaches _ (space.complement coveredMeasurable) restPositive
    input with ⟨count, reached⟩
  let mass := iterate kernel (count + 1) input (Set.complement covered)
  have massFinite : ENNReal.Finite mass := ENNReal.finite_of_le
    ((iterate_isProbability kernel markov (count + 1) input).apply_le_one _)
    True.intro
  rcases ENNReal.exists_positive_scale finite.univ_finite
      (ENNReal.half_finite.mpr massFinite) (ENNReal.half_positive reached) with
    ⟨factor, factorFinite, factorPositive, factorBound⟩
  rcases ENNReal.exists_finite_of_finite factorFinite with ⟨small, rfl⟩
  rcases scale_small factorPositive with ⟨index, less⟩
  have outside : Set.Subset (Set.complement covered)
      (Set.complement ((dominance generator markov finite count index).region input)) :=
    fun _ away inside => away ⟨count, index, inside⟩
  have upper := dominance_upper (dominance generator markov finite count index) input
    (space.complement coveredMeasurable) outside
  have scaled : ENNReal.le
      (ENNReal.mul (ENNReal.finite (scale index)) (reference (Set.complement covered)))
      (ENNReal.mul (ENNReal.finite small) (reference Set.univ)) :=
    ENNReal.mul_le_mul (less.1) (reference.mono (Set.subset_univ _))
  have chain := ENNReal.le_trans upper (ENNReal.le_trans scaled factorBound)
  exact (ENNReal.half_lt_self_of_positive_of_finite reached massFinite).2 chain

/-- Following a row of one dominance by a row of another dominates the scaled
meeting mass. -/
private theorem compose_lower (finite : Measure.IsFinite reference)
    {steps steps' : Nat} {weight weight' : NNReal}
    (first : Dominance kernel reference steps weight)
    (second : Dominance kernel reference steps' weight')
    (input : α) {event : Set α} (measurable : space.Measurable event) :
    ENNReal.le
      (ENNReal.mul (ENNReal.finite weight) (ENNReal.mul (ENNReal.finite weight')
        (lintegral reference (ennrealIndicator event
          (meeting reference first.region second.region input)))))
      (iterate kernel (steps + steps') input event) := by
  have row := row_measurable first.measurable input
  have outer := lintegral_mono_measure (fun middle => iterate kernel steps' middle event)
    (Measure.smul (ENNReal.finite weight) (reference.restrict (first.region input)))
    (iterate kernel steps input) (fun set setMeasurable => by
      rw [Measure.smul_apply_measurable _ _ setMeasurable,
        Measure.restrict_apply _ _ setMeasurable]
      exact dominance_lower first input setMeasurable)
  rw [lintegral_smul_measure, ← comp_apply_measurable _ _ _ measurable, ← iterate_add,
    ← lintegral_indicator reference _ row] at outer
  have beyond : ENNRealMeasurable space
      (fun middle => reference (Set.inter event (second.region middle))) :=
    section_measurable (relation := fun middle => Set.inter event (second.region middle))
      finite ((Space.product space space).inter
        (Space.second_measurable space space measurable) second.measurable)
  have inner : ENNReal.le
      (lintegral reference (ennrealIndicator (first.region input)
        (fun middle => ENNReal.mul (ENNReal.finite weight')
          (reference (Set.inter event (second.region middle))))))
      (lintegral reference (ennrealIndicator (first.region input)
        (fun middle => iterate kernel steps' middle event))) := by
    apply lintegral_mono
    intro middle
    by_cases inside : first.region input middle
    · simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left inside]
      exact dominance_lower second middle measurable
    · simp only [ennrealIndicator, ennrealPiecewise, ite_eq_right inside]
      exact ENNReal.le_refl _
  have pulled : ennrealIndicator (first.region input)
      (fun middle => ENNReal.mul (ENNReal.finite weight')
        (reference (Set.inter event (second.region middle)))) =
      fun middle => ENNReal.mul (ENNReal.finite weight')
        (ennrealIndicator (first.region input)
          (fun middle => reference (Set.inter event (second.region middle))) middle) := by
    funext middle
    by_cases inside : first.region input middle
    · simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left inside]
    · simp only [ennrealIndicator, ennrealPiecewise, ite_eq_right inside, ENNReal.mul_zero]
  rw [pulled, lintegral_smul reference _ (ENNRealMeasurable.indicator row beyond),
    swap_section finite second.measurable row measurable] at inner
  exact ENNReal.le_trans (ENNReal.mul_le_mul_left inner _) outer

end Rows

/-! ### Matching -/

section Matching

variable {kernel : Kernel space space} {reference : Measure space}

/-- A charged region covered by countably many pieces charges one of them. -/
private theorem exists_charged_piece {region : Set α}
    (charged : ENNReal.lt ENNReal.zero (reference region))
    (pieces : Nat → Nat → Set α)
    (covers : ∀ input, region input → ∃ count index, pieces count index input) :
    ∃ count index, ENNReal.lt ENNReal.zero
      (reference (Set.inter region (pieces count index))) := by
  apply Classical.byContradiction
  intro none
  have unionNull : reference.NullSet (Set.iUnion fun count => Set.iUnion fun index =>
      Set.inter region (pieces count index)) :=
    Measure.NullSet.iUnion fun count => Measure.NullSet.iUnion fun index => by
      apply Classical.byContradiction
      intro positive
      exact none ⟨count, index, ENNReal.zero_lt_iff_ne_zero.mpr positive⟩
  have null : reference.NullSet region := by
    apply unionNull.mono
    intro input member
    rcases covers input member with ⟨count, index, inside⟩
    exact ⟨count, index, member, inside⟩
  exact (ENNReal.zero_lt_iff_ne_zero.mp charged) null

/-- Tonelli moves a charge on rows to a charge on columns. -/
private theorem columns_charged (finite : Measure.IsFinite reference)
    {relation : α → Set α}
    (measurable : (Space.product space space).Measurable (pairs relation))
    (charged : ENNReal.lt ENNReal.zero
      (reference (fun row => ENNReal.lt ENNReal.zero (reference (relation row))))) :
    ENNReal.lt ENNReal.zero
      (reference (fun last => ENNReal.lt ENNReal.zero (reference (column relation last)))) := by
  have rowsPositive := lintegral_positive reference charged
    (section_measurable finite measurable) (fun _ member => member)
  have swapped := swap_section finite measurable space.univ space.univ
  simp only [Set.inter_univ_left, indicator_univ] at swapped
  rw [swapped] at rowsPositive
  exact charged_of_lintegral_positive reference rowsPositive

/-- Charged columns of the first relation that land on charged rows of the
second give a charged meeting mass. -/
private theorem meetingMass_positive (finite : Measure.IsFinite reference)
    {first second : α → Set α}
    (firstMeasurable : (Space.product space space).Measurable (pairs first))
    (secondMeasurable : (Space.product space space).Measurable (pairs second))
    (matched : ENNReal.lt ENNReal.zero (reference (Set.inter
      (fun last => ENNReal.lt ENNReal.zero (reference (column first last)))
      (fun middle => ENNReal.lt ENNReal.zero (reference (second middle)))))) :
    ENNReal.lt ENNReal.zero (meetingMass reference first second) := by
  have landing : space.Measurable
      (fun middle => ENNReal.lt ENNReal.zero (reference (second middle))) :=
    section_measurable finite secondMeasurable ENNReal.zero
  have reached := swap_section finite firstMeasurable space.univ landing
  simp only [Set.inter_univ_left, indicator_univ] at reached
  have reachedPositive : ENNReal.lt ENNReal.zero (lintegral reference
      (ennrealIndicator (fun middle => ENNReal.lt ENNReal.zero (reference (second middle)))
        (fun last => reference (column first last)))) := by
    apply lintegral_positive reference matched
      (ENNRealMeasurable.indicator landing (column_section_measurable finite firstMeasurable))
    intro last member
    rw [ennrealIndicator, ennrealPiecewise, ite_eq_left member.2]
    exact member.1
  rw [← reached] at reachedPositive
  have startsCharged := charged_of_lintegral_positive reference reachedPositive
  have innerMeasurable : ENNRealMeasurable space
      (fun row => lintegral reference (meeting reference first second row)) :=
    Kernel.lintegral_measurable_joint (Kernel.const space reference)
      (Kernel.IsSFinite.const space (Measure.SFinite.ofFinite finite))
      (meeting_measurable finite firstMeasurable secondMeasurable)
  apply lintegral_positive reference startsCharged innerMeasurable
  intro row member
  rw [lintegral_meeting finite firstMeasurable secondMeasurable row]
  apply lintegral_positive reference member
    (ENNRealMeasurable.indicator (row_measurable firstMeasurable row)
      (section_measurable finite secondMeasurable))
  intro middle inside
  rw [ennrealIndicator, ennrealPiecewise, ite_eq_left inside.2]
  exact inside.1

/-- Some pair of dominance rows has a charged meeting mass. -/
private theorem exists_matched_rows (generator : Space.CountableGenerator space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (irreducible : MeasureIrreducible kernel reference)
    (finite : Measure.IsFinite reference) :
    ∃ count index count' index', ENNReal.lt ENNReal.zero
      (meetingMass reference (dominance generator markov finite count index).region
        (dominance generator markov finite count' index').region) := by
  let charged : Nat → Nat → Set α := fun count index input =>
    ENNReal.lt ENNReal.zero
      (reference ((dominance generator markov finite count index).region input))
  have covers : ∀ input, ∃ count index, charged count index input :=
    fun input => exists_charged_row generator markov irreducible finite input
  rcases exists_charged_piece irreducible.nonzero charged (fun input _ => covers input) with
    ⟨count, index, rowsCharged⟩
  rw [Set.inter_univ_left] at rowsCharged
  have columns := columns_charged finite
    (dominance generator markov finite count index).measurable rowsCharged
  rcases exists_charged_piece columns charged (fun input _ => covers input) with
    ⟨count', index', matched⟩
  exact ⟨count, index, count', index', meetingMass_positive finite
    (dominance generator markov finite count index).measurable
    (dominance generator markov finite count' index').measurable matched⟩

end Matching

/-! ### Pigeonhole -/

section Pigeonhole

variable {reference : Measure space}

private theorem le_of_not_lt {left right : ENNReal}
    (above : ¬ ENNReal.lt left right) : ENNReal.le right left := by
  rcases ENNReal.le_total right left with below | over
  · exact below
  · exact Classical.byContradiction fun missing => above ⟨over, missing⟩

/-- Five eighths of a value stay below it. -/
private theorem five_eighths_le (value : ENNReal) :
    ENNReal.le
      (ENNReal.add
        (ENNReal.add (ENNReal.half (ENNReal.half (ENNReal.half value)))
          (ENNReal.add (ENNReal.half (ENNReal.half (ENNReal.half value)))
            (ENNReal.half (ENNReal.half (ENNReal.half value)))))
        (ENNReal.add (ENNReal.half (ENNReal.half (ENNReal.half value)))
          (ENNReal.half (ENNReal.half (ENNReal.half value)))))
      value := by
  have eighth : ENNReal.le (ENNReal.half (ENNReal.half (ENNReal.half value)))
      (ENNReal.half (ENNReal.half value)) := by
    have bound := ENNReal.le_self_add (ENNReal.half (ENNReal.half (ENNReal.half value)))
      (ENNReal.half (ENNReal.half (ENNReal.half value)))
    rw [ENNReal.half_add_half] at bound
    exact bound
  have quarter : ENNReal.le (ENNReal.half (ENNReal.half value))
      (ENNReal.half value) := by
    have bound := ENNReal.le_self_add (ENNReal.half (ENNReal.half value))
      (ENNReal.half (ENNReal.half value))
    rw [ENNReal.half_add_half] at bound
    exact bound
  rw [ENNReal.half_add_half]
  have step := ENNReal.add_le_add
    (ENNReal.add_le_add_right eighth (ENNReal.half (ENNReal.half value)))
    (ENNReal.le_refl (ENNReal.half (ENNReal.half value)))
  rw [ENNReal.half_add_half] at step
  have last := ENNReal.add_le_add_left quarter (ENNReal.half value)
  rw [ENNReal.half_add_half] at last
  exact ENNReal.le_trans step last

/-- A charged meeting mass is bounded below uniformly on a pair of charged
cells. Approximating rows and columns by the countable algebra, if every pair
of charged cells met thinly the mass would fall below itself. -/
private theorem exists_uniform_meeting (generator : Space.CountableGenerator space)
    (finite : Measure.IsFinite reference) {first second : α → Set α}
    (firstMeasurable : (Space.product space space).Measurable (pairs first))
    (secondMeasurable : (Space.product space space).Measurable (pairs second))
    (charged : ENNReal.lt ENNReal.zero (meetingMass reference first second)) :
    ∃ (rows columns : Set α) (floor : NNReal),
      space.Measurable rows ∧ space.Measurable columns ∧
      NNReal.lt NNReal.zero floor ∧
      ENNReal.lt ENNReal.zero (reference rows) ∧
      ENNReal.lt ENNReal.zero (reference columns) ∧
      ∀ row, rows row → ∀ last, columns last →
        ENNReal.le (ENNReal.finite floor) (meeting reference first second row last) := by
  let algebra := generator.algebra
  have totalFinite : ENNReal.Finite (reference Set.univ) := finite.univ_finite
  have massFinite : ENNReal.Finite (meetingMass reference first second) := by
    have inner : ∀ row, ENNReal.le
        (lintegral reference (meeting reference first second row))
        (ENNReal.mul (reference Set.univ) (reference Set.univ)) := by
      intro row
      have bound := lintegral_mono reference
        (fun last => reference.mono (Set.subset_univ
          (Set.inter (first row) (column second last))))
      rw [lintegral_const] at bound
      exact bound
    have outer := lintegral_mono reference inner
    rw [lintegral_const] at outer
    exact ENNReal.finite_of_le outer (ENNReal.mul_finite
      (ENNReal.mul_finite totalFinite totalFinite) totalFinite)
  rcases ENNReal.exists_positive_scale (ENNReal.mul_finite totalFinite totalFinite)
      (ENNReal.half_finite.mpr massFinite) (ENNReal.half_positive charged) with
    ⟨factor, factorFinite, factorPositive, factorBound⟩
  rcases ENNReal.exists_finite_of_finite factorFinite with ⟨small, rfl⟩
  let floor := NNReal.half (NNReal.half (NNReal.half small))
  have floorPositive : NNReal.lt NNReal.zero floor :=
    NNReal.half_positive (NNReal.half_positive (NNReal.half_positive factorPositive))
  let radius := ENNReal.finite floor
  -- Cells of rows and columns near each member of the algebra.
  let rowCell : Nat → Set α := fun index => Set.complement fun row =>
    ENNReal.lt radius (reference.setDistance (first row) (algebra.sets index))
  let columnCell : Nat → Set α := fun index => Set.complement fun last =>
    ENNReal.lt radius (reference.setDistance (column second last) (algebra.sets index))
  have rowCellMeasurable : ∀ index, space.Measurable (rowCell index) := fun index =>
    space.complement (section_measurable
      (relation := fun row => Set.symmDiff (first row) (algebra.sets index)) finite
      (Space.symmDiff_measurable firstMeasurable
        (Space.second_measurable space space (algebra.measurable index))) radius)
  have columnCellMeasurable : ∀ index, space.Measurable (columnCell index) := fun index =>
    space.complement (section_measurable
      (relation := fun last => Set.symmDiff (column second last) (algebra.sets index))
      finite
      (Space.symmDiff_measurable (transpose_measurable secondMeasurable)
        (Space.second_measurable space space (algebra.measurable index))) radius)
  have rowCovered : ∀ row, ∃ index, rowCell index row := by
    intro row
    rcases Measure.approximable_of_measurable finite algebra
        (row_measurable firstMeasurable row) floor floorPositive with ⟨index, near⟩
    exact ⟨index, fun far => far.2 near⟩
  have columnCovered : ∀ last, ∃ index, columnCell index last := by
    intro last
    rcases Measure.approximable_of_measurable finite algebra
        (column_measurable secondMeasurable last) floor floorPositive with
      ⟨index, near⟩
    exact ⟨index, fun far => far.2 near⟩
  have good : ∃ index index',
      ENNReal.lt ENNReal.zero (reference (rowCell index)) ∧
      ENNReal.lt ENNReal.zero (reference (columnCell index')) ∧
      ENNReal.lt (ENNReal.add radius (ENNReal.add radius radius))
        (reference (Set.inter (algebra.sets index) (algebra.sets index'))) := by
    apply Classical.byContradiction
    intro none
    let rowsNull : Set α := Set.iUnion fun index =>
      Set.inter (rowCell index) (fun _ => reference (rowCell index) = ENNReal.zero)
    let columnsNull : Set α := Set.iUnion fun index =>
      Set.inter (columnCell index) (fun _ => reference (columnCell index) = ENNReal.zero)
    have rowsNullNull : reference.NullSet rowsNull :=
      Measure.NullSet.iUnion fun index => by
        by_cases vanished : reference (rowCell index) = ENNReal.zero
        · exact Measure.NullSet.mono vanished (fun _ member => member.1)
        · exact Measure.NullSet.mono reference.empty_apply
            (fun _ member => (vanished member.2).elim)
    have columnsNullNull : reference.NullSet columnsNull :=
      Measure.NullSet.iUnion fun index => by
        by_cases vanished : reference (columnCell index) = ENNReal.zero
        · exact Measure.NullSet.mono vanished (fun _ member => member.1)
        · exact Measure.NullSet.mono reference.empty_apply
            (fun _ member => (vanished member.2).elim)
    have rowFound : ∀ row, ¬ rowsNull row → ∃ index, rowCell index row ∧
        ENNReal.lt ENNReal.zero (reference (rowCell index)) := by
      intro row away
      rcases rowCovered row with ⟨index, member⟩
      exact ⟨index, member, ENNReal.zero_lt_iff_ne_zero.mpr fun vanished =>
        away ⟨index, member, vanished⟩⟩
    have columnFound : ∀ last, ¬ columnsNull last → ∃ index, columnCell index last ∧
        ENNReal.lt ENNReal.zero (reference (columnCell index)) := by
      intro last away
      rcases columnCovered last with ⟨index, member⟩
      exact ⟨index, member, ENNReal.zero_lt_iff_ne_zero.mpr fun vanished =>
        away ⟨index, member, vanished⟩⟩
    let bound := ENNReal.add (ENNReal.add radius (ENNReal.add radius radius))
      (ENNReal.add radius radius)
    have meetingSmall : ∀ row, ¬ rowsNull row → ∀ last, ¬ columnsNull last →
        ENNReal.le (meeting reference first second row last) bound := by
      intro row rowAway last lastAway
      rcases rowFound row rowAway with ⟨index, rowMember, rowCharged⟩
      rcases columnFound last lastAway with ⟨index', lastMember, lastCharged⟩
      have cellsSmall := le_of_not_lt fun large =>
        none ⟨index, index', rowCharged, lastCharged, large⟩
      exact ENNReal.le_trans
        (inter_le_add reference (first row) (column second last)
          (algebra.sets index) (algebra.sets index'))
        (ENNReal.add_le_add cellsSmall
          (ENNReal.add_le_add (le_of_not_lt rowMember) (le_of_not_lt lastMember)))
    have innerSmall : ∀ row, ¬ rowsNull row → ENNReal.le
        (lintegral reference (meeting reference first second row))
        (ENNReal.mul bound (reference Set.univ)) := by
      intro row away
      have bounded := lintegral_mono_ae (measure := reference)
        (left := meeting reference first second row) (right := fun _ => bound)
        (Measure.NullSet.mono columnsNullNull (fun last over =>
          Classical.byContradiction fun lastAway =>
            over (meetingSmall row away last lastAway)))
      rw [lintegral_const] at bounded
      exact bounded
    have outerSmall := lintegral_mono_ae (measure := reference)
      (left := fun row => lintegral reference (meeting reference first second row))
      (right := fun _ => ENNReal.mul bound (reference Set.univ))
      (Measure.NullSet.mono rowsNullNull (fun row over =>
        Classical.byContradiction fun rowAway => over (innerSmall row rowAway)))
    rw [lintegral_const, ENNReal.mul_assoc] at outerSmall
    have scaled := ENNReal.mul_le_mul_right (five_eighths_le (ENNReal.finite small))
      (ENNReal.mul (reference Set.univ) (reference Set.univ))
    have chain := ENNReal.le_trans outerSmall (ENNReal.le_trans scaled factorBound)
    exact (ENNReal.half_lt_self_of_positive_of_finite charged massFinite).2 chain
  rcases good with ⟨index, index', rowCharged, columnCharged, large⟩
  refine ⟨rowCell index, columnCell index', floor, rowCellMeasurable index,
    columnCellMeasurable index', floorPositive, rowCharged, columnCharged, ?_⟩
  intro row rowMember last lastMember
  have near := inter_le_add reference (algebra.sets index) (algebra.sets index')
    (first row) (column second last)
  rw [Measure.setDistance_comm reference (algebra.sets index),
    Measure.setDistance_comm reference (algebra.sets index')] at near
  rcases ENNReal.le_total radius (meeting reference first second row last) with
    enough | short
  · exact enough
  · exfalso
    exact large.2 (ENNReal.le_trans near (ENNReal.add_le_add short
      (ENNReal.add_le_add (le_of_not_lt rowMember) (le_of_not_lt lastMember))))

end Pigeonhole

/-! ### Assembly -/

section Assembly

variable {kernel : Kernel space space} {reference : Measure space}

/-- A uniform meeting on a pair of charged cells minorizes the composed iterate
on the first cell by the normalized reference on the second. -/
private theorem minorized_of_meeting (finite : Measure.IsFinite reference)
    {steps steps' : Nat} {weight weight' : NNReal}
    (first : Dominance kernel reference steps weight)
    (second : Dominance kernel reference steps' weight')
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (stepsPositive : 0 < steps)
    (weightPositive : NNReal.lt NNReal.zero weight)
    (weightPositive' : NNReal.lt NNReal.zero weight')
    {rows columns : Set α} {floor : NNReal}
    (columnsMeasurable : space.Measurable columns)
    (floorPositive : NNReal.lt NNReal.zero floor)
    (rowsCharged : ENNReal.lt ENNReal.zero (reference rows))
    (columnsCharged : ENNReal.lt ENNReal.zero (reference columns))
    (uniform : ∀ row, rows row → ∀ last, columns last →
      ENNReal.le (ENNReal.finite floor)
        (meeting reference first.region second.region row last)) :
    ∃ scaled minorant,
      MinorizationOn kernel rows (steps + steps') scaled minorant := by
  rcases ENNReal.exists_finite_of_finite (ENNReal.finite_of_le
      (reference.mono (Set.subset_univ columns)) finite.univ_finite) with
    ⟨mass, massEq⟩
  have massPositive : NNReal.lt NNReal.zero mass := by
    rw [massEq] at columnsCharged
    exact columnsCharged
  have massNonzero : mass ≠ NNReal.zero := by
    intro vanished
    rw [vanished] at massPositive
    exact massPositive.2 massPositive.1
  have total : (reference.restrict columns) Set.univ = ENNReal.finite mass := by
    rw [Measure.restrict_apply_univ, massEq]
  have normalizable : Measure.IsNormalizable (reference.restrict columns) :=
    ⟨finite.restrict columns, by
      rw [total]
      intro vanished
      exact massNonzero (ENNReal.finite_injective vanished)⟩
  let minorant : Giry.Law space :=
    ⟨Measure.normalize (reference.restrict columns) normalizable,
      Measure.normalize_isProbability _ normalizable⟩
  let scaled := NNReal.mul (NNReal.mul (NNReal.mul weight weight') floor) mass
  have cancel : NNReal.mul scaled (NNReal.div NNReal.one mass) =
      NNReal.mul (NNReal.mul weight weight') floor := by
    rw [NNReal.mul_assoc, NNReal.mul_comm mass, NNReal.div_mul_cancel NNReal.one massNonzero,
      NNReal.mul_one]
  have lower : ∀ input, rows input → ∀ event, space.Measurable event →
      ENNReal.le ((Measure.smul (ENNReal.finite scaled) minorant.val) event)
        (iterate kernel (steps + steps') input event) := by
    intro input member event measurable
    have both := space.inter measurable columnsMeasurable
    change ENNReal.le ((Measure.smul (ENNReal.finite scaled)
      (Measure.normalize (reference.restrict columns) normalizable)) event) _
    rw [Measure.normalize_eq_of_total_eq _ normalizable total,
      Measure.smul_apply_measurable _ _ measurable, Measure.smul_apply_measurable _ _ measurable,
      Measure.restrict_apply _ _ measurable, ← ENNReal.mul_assoc, ENNReal.finite_mul_finite,
      cancel, ← ENNReal.finite_mul_finite, ← ENNReal.finite_mul_finite, ENNReal.mul_assoc,
      ENNReal.mul_assoc]
    have meets := lintegral_lower_on reference both
      (function := ennrealIndicator event
        (meeting reference first.region second.region input))
      (fun last inside => by
        rw [ennrealIndicator, ennrealPiecewise, ite_eq_left inside.1]
        exact uniform input member last inside.2)
    exact ENNReal.le_trans
      (ENNReal.mul_le_mul_left (ENNReal.mul_le_mul_left meets _) _)
      (compose_lower finite first second input measurable)
  refine ⟨scaled, minorant, ⟨markov,
    Nat.lt_of_lt_of_le stepsPositive (Nat.le_add_right steps steps'),
    NNReal.mul_positive (NNReal.mul_positive
      (NNReal.mul_positive weightPositive weightPositive') floorPositive) massPositive,
    ?_, lower⟩⟩
  rcases Measure.exists_mem_of_positive reference rowsCharged with ⟨start, member⟩
  have whole := lower start member Set.univ space.univ
  rw [Measure.smul_apply_measurable _ _ space.univ, minorant.property.univ_eq_one,
    ENNReal.mul_one,
    (iterate_isProbability kernel markov (steps + steps') start).univ_eq_one] at whole
  exact whole

end Assembly

/-- A Markov kernel on a countably generated space that is irreducible against a
finite reference has a small set that the reference and its own minorant both
charge. -/
public theorem exists_positive_small_set {kernel : Kernel space space}
    {reference : Measure space} (generator : Space.CountableGenerator space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (irreducible : MeasureIrreducible kernel reference)
    (finite : Measure.IsFinite reference) :
    ∃ (region : Set α) (steps : Nat) (weight : NNReal)
      (minorant : Giry.Law space),
      space.Measurable region ∧
      MinorizationOn kernel region steps weight minorant ∧
      ENNReal.lt ENNReal.zero (reference region) ∧
      ENNReal.lt ENNReal.zero (minorant.val region) := by
  rcases exists_matched_rows generator markov irreducible finite with
    ⟨count, index, count', index', matched⟩
  rcases exists_uniform_meeting generator finite
      (dominance generator markov finite count index).measurable
      (dominance generator markov finite count' index').measurable matched with
    ⟨rows, columns, floor, rowsMeasurable, columnsMeasurable, floorPositive,
      rowsCharged, columnsCharged, uniform⟩
  rcases minorized_of_meeting finite (dominance generator markov finite count index)
      (dominance generator markov finite count' index') markov (Nat.succ_pos count)
      (scale_positive index) (scale_positive index') columnsMeasurable floorPositive
      rowsCharged columnsCharged uniform with
    ⟨weight, minorant, minor⟩
  rcases irreducible.reaches_from markov minorant rowsMeasurable rowsCharged with
    ⟨shift, reached⟩
  exact ⟨rows, _, weight, _, rowsMeasurable, minor.shift (shift + 1), rowsCharged,
    reached⟩

end Problib.Measure.Kernel
