module

public import Problib.Measure.Memo.Cylinder
public import Problib.Measure.Extended.Unit
public import Problib.Measure.Kernel.Product.Transport
public import Problib.Real.Extended.Power
public import Problib.Real.Extended.Approximation

set_option autoImplicit false

/-!
# Binary values of fair tables

A fair table read off one uniform seed is the seed's binary expansion: each
reading halves the cell that holds the seed. The supremum of the lower ends of
the selected cells is a measurable binary value that recovers every seed below
one, so the binary value of the fair table law is the uniform law.
-/

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Real.Construction
open Problib.Measure.Real Dedekind

/-- One half, the bias of a fair coin. -/
@[expose] noncomputable def fair : UnitInterval := unitClamp (ENNReal.half ENNReal.one)

private theorem half_lt_one : ENNReal.lt (ENNReal.half ENNReal.one) ENNReal.one :=
  ENNReal.half_lt_self_of_positive_of_finite ENNReal.one_positive True.intro

theorem ofReal_fair : ENNReal.ofReal fair.val = ENNReal.half ENNReal.one :=
  ofReal_unitClamp_of_le half_lt_one.1

/-- Each reading of a fair coin weighs one half. -/
theorem weight_fair (value : Bool) :
    ENNReal.ofReal (Cell.weight fair value) = ENNReal.half ENNReal.one := by
  cases value with
  | true => exact ofReal_fair
  | false =>
      apply ENNReal.add_left_cancel_of_finite (factor := ENNReal.half ENNReal.one)
        (ENNReal.half_finite.mpr True.intro)
      rw [ENNReal.half_add_half, ENNReal.add_comm, ← ofReal_fair]
      exact weight_sum fair

/-- The first `count` readings of a table, in order. -/
@[expose] def prefixWord (table : Table) : Nat → List Bool
  | 0 => []
  | count + 1 => table 0 :: prefixWord (fun n => table (n + 1)) count

theorem prefix_prefixWord (table : Table) (count : Nat) :
    Prefix (prefixWord table count) table := by
  induction count generalizing table with
  | zero => trivial
  | succ count induction => exact ⟨rfl, induction _⟩

theorem length_prefixWord (table : Table) (count : Nat) :
    (prefixWord table count).length = count := by
  induction count generalizing table with
  | zero => rfl
  | succ count induction => exact congrArg Nat.succ (induction _)

theorem wordWeight_fair (word : List Bool) :
    wordWeight (fun _ => fair) word = ENNReal.pow (ENNReal.half ENNReal.one) word.length := by
  induction word with
  | nil => rfl
  | cons value rest induction =>
      rw [wordWeight, induction, weight_fair, List.length_cons, ENNReal.pow_succ]

/-- The fair cell selected by a word of readings has width one half per
reading. -/
theorem width_fair (word : List Bool) :
    ENNReal.ofReal (descend (fun _ => fair) Cell.whole word).width =
      ENNReal.pow (ENNReal.half ENNReal.one) word.length := by
  rw [← Cell.mass, descend_mass, mass_whole, ENNReal.mul_one, wordWeight_fair]

private theorem upper_eq (cell : Cell) : cell.upper = add cell.lower cell.width := by
  change cell.upper = add cell.lower (sub cell.upper cell.lower)
  rw [Dedekind.sub_eq_add_neg, Dedekind.add_left_comm, Dedekind.add_neg, Dedekind.add_zero]

universe u
variable {α : Type u} {source : Space α}

/-- The ends of the fair cell selected by the first readings of a table are
measurable in the table and the starting cell. -/
theorem descend_measurable {cell : α → Cell} {table : α → Table}
    (lowerMeasurable : MeasurableMap source borel fun x => (cell x).lower)
    (upperMeasurable : MeasurableMap source borel fun x => (cell x).upper)
    (tableMeasurable : MeasurableMap source tableSpace table) (count : Nat) :
    MeasurableMap source borel
        (fun x => (descend (fun _ => fair) (cell x) (prefixWord (table x) count)).lower) ∧
      MeasurableMap source borel
        (fun x => (descend (fun _ => fair) (cell x) (prefixWord (table x) count)).upper) := by
  induction count generalizing cell table with
  | zero => exact ⟨lowerMeasurable, upperMeasurable⟩
  | succ count induction =>
      have readingMeasurable : source.Measurable (fun x => table x 0 = true) :=
        tableMeasurable (Space.coordinate_measurable (fun _ : Nat => Space.discrete Bool) 0
          (Space.discrete_measurable (Set.singleton true)))
      have cutMeasurable : MeasurableMap source borel (fun x => (cell x).cut fair) :=
        measurable_add lowerMeasurable
          (measurable_mul (MeasurableMap.constant _ _ fair.val)
            (measurable_sub upperMeasurable lowerMeasurable))
      have branchLower : (fun x => ((cell x).branch fair (table x 0)).lower) =
          fun x => @ite Carrier (table x 0 = true) (Classical.propDecidable _)
            (cell x).lower ((cell x).cut fair) := by
        funext x
        cases table x 0 <;> simp [Cell.branch]
      have branchUpper : (fun x => ((cell x).branch fair (table x 0)).upper) =
          fun x => @ite Carrier (table x 0 = true) (Classical.propDecidable _)
            ((cell x).cut fair) (cell x).upper := by
        funext x
        cases table x 0 <;> simp [Cell.branch]
      have lowerStep : MeasurableMap source borel
          (fun x => ((cell x).branch fair (table x 0)).lower) := by
        rw [branchLower]
        exact fun {set} => measurable_piecewise readingMeasurable lowerMeasurable cutMeasurable
          (set := set)
      have upperStep : MeasurableMap source borel
          (fun x => ((cell x).branch fair (table x 0)).upper) := by
        rw [branchUpper]
        exact fun {set} => measurable_piecewise readingMeasurable cutMeasurable upperMeasurable
          (set := set)
      exact induction (cell := fun x => (cell x).branch fair (table x 0))
        (table := fun x n => table x (n + 1)) lowerStep upperStep
        (MeasurableMap.comp (Space.pi_reindex (fun _ : Nat => Space.discrete Bool) Nat.succ)
          tableMeasurable)

/-- The binary value of a table: the supremum of the lower ends of the fair
cells that its readings select. -/
@[expose] noncomputable def binaryValue (table : Table) : UnitInterval :=
  unitClamp (ENNReal.iSup fun count =>
    ENNReal.ofReal (descend (fun _ => fair) Cell.whole (prefixWord table count)).lower)

theorem binaryValue_measurable : MeasurableMap tableSpace unitBorel binaryValue :=
  MeasurableMap.comp unitClamp_measurable (ENNRealMeasurable.measurableMap
    (ENNRealMeasurable.iSup fun count => ENNRealMeasurable.comp ofReal_measurable
      (descend_measurable (cell := fun _ => Cell.whole) (MeasurableMap.constant _ _ _)
        (MeasurableMap.constant _ _ _) (MeasurableMap.identity _) count).1))

/-- The fair readings of a seed below one have that seed as their binary
value. -/
theorem binaryValue_decode {seed : UnitInterval} (inside : Cell.whole.region seed) :
    binaryValue (decode (fun _ => fair) seed) = seed := by
  have contains : ∀ count, (descend (fun _ => fair) Cell.whole
      (prefixWord (decode (fun _ => fair) seed) count)).region seed := fun count =>
    (prefix_read _ _ seed inside _).mp (prefix_prefixWord _ count)
  have below : ∀ count, ENNReal.le
      (ENNReal.ofReal (descend (fun _ => fair) Cell.whole
        (prefixWord (decode (fun _ => fair) seed) count)).lower)
      (ENNReal.ofReal seed.val) := fun count => ENNReal.ofReal_monotone (contains count).1
  have above : ∀ count, ENNReal.le (ENNReal.ofReal seed.val)
      (ENNReal.add (ENNReal.ofReal (descend (fun _ => fair) Cell.whole
          (prefixWord (decode (fun _ => fair) seed) count)).lower)
        (ENNReal.pow (ENNReal.half ENNReal.one) count)) := by
    intro count
    have bound := ENNReal.ofReal_monotone (contains count).2.1
    rw [upper_eq, ENNReal.ofReal_add (Cell.nonnegative _) (Cell.width_nonnegative _), width_fair,
      length_prefixWord] at bound
    exact bound
  have supremum : ENNReal.iSup (fun count => ENNReal.ofReal (descend (fun _ => fair) Cell.whole
      (prefixWord (decode (fun _ => fair) seed) count)).lower) = ENNReal.ofReal seed.val := by
    apply ENNReal.le_antisymm (ENNReal.iSup_le below)
    apply ENNReal.le_of_forall_positive_le_add
    intro error positive
    obtain ⟨stage, small⟩ := ENNReal.pow_eventually_lt half_lt_one positive
    exact ENNReal.le_trans (above stage)
      (ENNReal.add_le_add
        (ENNReal.le_iSup (fun count => ENNReal.ofReal (descend (fun _ => fair) Cell.whole
          (prefixWord (decode (fun _ => fair) seed) count)).lower) stage)
        (small stage (Nat.le_refl stage)).1)
  unfold binaryValue
  rw [supremum]
  exact unitClamp_ofReal seed

/-- The binary value of the fair table law is the uniform law. -/
theorem law_fair_binaryValue :
    (law fun _ => fair).map binaryValue binaryValue_measurable = uniform01 := by
  have decodeMeasurable : MeasurableMap unitBorel tableSpace (decode fun _ => fair) :=
    decode_measurable (fun _ => MeasurableMap.constant _ _ fair) (MeasurableMap.identity _)
  exact (Measure.map_comp uniform01 (decode fun _ => fair) binaryValue decodeMeasurable
    binaryValue_measurable).trans ((Measure.map_congr_on uniform01 whole_complement_null
      (MeasurableMap.comp binaryValue_measurable decodeMeasurable) (MeasurableMap.identity _)
      fun _ inside => binaryValue_decode inside).trans (Measure.map_id uniform01))

end
end Problib.Measure.Memo
