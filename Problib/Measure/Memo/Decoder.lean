module

public import Problib.Measure.Memo.Interval
public import Problib.Measure.Pi

set_option autoImplicit false

namespace Problib.Measure.Memo
public section
open Problib.Real Problib.Real.Construction
open Problib.Measure.Real
open Dedekind

abbrev Table := Nat → Bool
abbrev Bias := Nat → UnitInterval

@[expose] def tableSpace : Space Table := Space.pi (fun _ => Space.discrete Bool)

@[expose] noncomputable def choice (cell : Cell) (bias : UnitInterval) (seed : UnitInterval) : Bool :=
  boolIndicator (fun point : UnitInterval => lt point.val (cell.cut bias)) seed

/-- A coordinate decoder terminates after inspecting its finite prefix. -/
@[expose] noncomputable def read (bias : Bias) (cell : Cell) (seed : UnitInterval) : Nat → Bool
  | 0 => choice cell (bias 0) seed
  | n + 1 => read (fun k => bias (k + 1)) (cell.branch (bias 0) (choice cell (bias 0) seed)) seed n

@[expose] def Prefix : List Bool → Table → Prop
  | [], _ => True
  | value :: rest, table => table 0 = value ∧ Prefix rest (fun n => table (n + 1))

@[expose] noncomputable def descend (bias : Bias) (cell : Cell) : List Bool → Cell
  | [] => cell
  | value :: rest => descend (fun k => bias (k + 1)) (cell.branch (bias 0) value) rest

theorem descend_subset (bias : Bias) (cell : Cell) (word : List Bool) :
    Set.Subset (descend bias cell word).region cell.region := by
  induction word generalizing bias cell with
  | nil => exact Set.subset_refl _
  | cons value rest induction =>
      exact Set.subset_trans (induction _ _) (cell.branch_subset _ _)

theorem prefix_read (bias : Bias) (cell : Cell) (seed : UnitInterval)
    (inside : cell.region seed) (word : List Bool) :
    Prefix word (read bias cell seed) ↔ (descend bias cell word).region seed := by
  induction word generalizing bias cell with
  | nil => exact ⟨fun _ => inside, fun _ => trivial⟩
  | cons value rest induction =>
      change (choice cell (bias 0) seed = value ∧ Prefix rest
        (read (fun k => bias (k + 1)) (cell.branch (bias 0) (choice cell (bias 0) seed)) seed)) ↔ _
      constructor
      · rintro ⟨same, prefixHolds⟩
        rw [same] at prefixHolds
        exact (induction _ _ ((cell.branch_region _ seed inside value).mpr same)).mp prefixHolds
      · intro member
        have branch := descend_subset (fun k => bias (k + 1)) (cell.branch (bias 0) value) rest member
        have same : choice cell (bias 0) seed = value := (cell.branch_region _ seed inside value).mp branch
        refine ⟨same, ?_⟩
        rw [same]
        exact (induction _ _ branch).mpr member

universe u
variable {α : Type u} {source : Space α}

private theorem branch_lower (cell : Cell) (bias : UnitInterval) (seed : UnitInterval) :
    (cell.branch bias (choice cell bias seed)).lower =
      @ite Carrier (lt seed.val (cell.cut bias)) (Classical.propDecidable _)
        cell.lower (cell.cut bias) := by
  classical
  by_cases below : lt seed.val (cell.cut bias) <;> simp [choice, boolIndicator, below, Cell.branch]

private theorem branch_upper (cell : Cell) (bias : UnitInterval) (seed : UnitInterval) :
    (cell.branch bias (choice cell bias seed)).upper =
      @ite Carrier (lt seed.val (cell.cut bias)) (Classical.propDecidable _)
        (cell.cut bias) cell.upper := by
  classical
  by_cases below : lt seed.val (cell.cut bias) <;> simp [choice, boolIndicator, below, Cell.branch]

/-- Joint measurability includes all captured parameters and the Uniform seed. -/
theorem read_measurable {bias : α → Bias} {cell : α → Cell} {seed : α → UnitInterval}
    (biasMeasurable : ∀ n, MeasurableMap source unitBorel (fun x => bias x n))
    (lowerMeasurable : MeasurableMap source borel (fun x => (cell x).lower))
    (upperMeasurable : MeasurableMap source borel (fun x => (cell x).upper))
    (seedMeasurable : MeasurableMap source unitBorel seed) (n : Nat) :
    MeasurableMap source (Space.discrete Bool) (fun x => read (bias x) (cell x) (seed x) n) := by
  induction n generalizing cell bias with
  | zero =>
      apply boolIndicator_measurable
      exact measurable_lt (unitInclusion_measurable.comp seedMeasurable)
        (measurable_add lowerMeasurable
          (measurable_mul (unitInclusion_measurable.comp (biasMeasurable 0))
            (measurable_sub upperMeasurable lowerMeasurable)))
  | succ n induction =>
      have cutMeasurable : MeasurableMap source borel (fun x => (cell x).cut (bias x 0)) :=
        measurable_add lowerMeasurable
          (measurable_mul (unitInclusion_measurable.comp (biasMeasurable 0))
            (measurable_sub upperMeasurable lowerMeasurable))
      have event := measurable_lt (unitInclusion_measurable.comp seedMeasurable) cutMeasurable
      apply induction (fun n => biasMeasurable (n + 1))
      · have equal : (fun x => ((cell x).branch (bias x 0) (choice (cell x) (bias x 0) (seed x))).lower) =
            (fun x => @ite Carrier (lt (seed x).val ((cell x).cut (bias x 0)))
              (Classical.propDecidable _) (cell x).lower ((cell x).cut (bias x 0))) :=
          funext fun x => branch_lower _ _ _
        rw [equal]
        exact fun {set} => measurable_piecewise event lowerMeasurable cutMeasurable (set := set)
      · have equal : (fun x => ((cell x).branch (bias x 0) (choice (cell x) (bias x 0) (seed x))).upper) =
            (fun x => @ite Carrier (lt (seed x).val ((cell x).cut (bias x 0)))
              (Classical.propDecidable _) ((cell x).cut (bias x 0)) (cell x).upper) :=
          funext fun x => branch_upper _ _ _
        rw [equal]
        exact fun {set} => measurable_piecewise event cutMeasurable upperMeasurable (set := set)

@[expose] noncomputable def decode (bias : Bias) (seed : UnitInterval) : Table :=
  read bias Cell.whole seed

theorem decode_measurable {bias : α → Bias} {seed : α → UnitInterval}
    (biasMeasurable : ∀ n, MeasurableMap source unitBorel (fun x => bias x n))
    (seedMeasurable : MeasurableMap source unitBorel seed) :
    MeasurableMap source tableSpace (fun x => decode (bias x) (seed x)) :=
  Space.pi_measurable fun n => read_measurable biasMeasurable
    (MeasurableMap.constant _ _ zero) (MeasurableMap.constant _ _ one) seedMeasurable n

end
end Problib.Measure.Memo
