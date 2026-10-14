module

public import Problib.Measure.Kernel.Chart.Basic

/-! # The selected stratum

A point may lie in the images of several charts. Each point is assigned to one
of them: the chart of lowest dimension, and among those the one of least index.
Assignment by a fixed order, rather than by a choice per point, keeps the
assignment jointly measurable in the parameter and the point, so the pieces it
cuts are measurable and the reference counts every point once.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Measure.Real (borel Carrier)

public section

universe u

variable {Θ : Type u} {parameter : Space Θ} {ambient : Nat}
  (family : Family parameter ambient)

/-- `first` comes no later than `second` in the order of (dimension, index). -/
@[expose] public def Family.Before (first second : Nat) : Prop :=
  family.dimension first < family.dimension second ∨
    (family.dimension first = family.dimension second ∧ first ≤ second)

/-- `index` is the selected stratum of `point` at `θ`: its chart's image holds
the point, and every chart whose image holds it comes no earlier. -/
@[expose] public def Family.Selected (index : Nat) (θ : Θ) (point : Fin ambient → Carrier) : Prop :=
  (family.chart index).member θ point ∧
    ∀ other, (family.chart other).member θ point → family.Before index other

private theorem implies_measurable {α : Type u} {space : Space α} {set : Set α}
    (measurable : space.Measurable set) (claim : Prop) :
    space.Measurable (fun value => set value → claim) := by
  classical
  by_cases holds : claim
  · have equal : (fun value => set value → claim) = Set.univ := by
      funext value
      exact propext ⟨fun _ => True.intro, fun _ _ => holds⟩
    rw [equal]
    exact space.univ
  · have equal : (fun value => set value → claim) = Set.complement set := by
      funext value
      exact propext ⟨fun implied member => holds (implied member),
        fun excluded member => (excluded member).elim⟩
    rw [equal]
    exact space.complement measurable

/-- The selected stratum is jointly measurable: a countable intersection of
membership tests. -/
public theorem Family.selected_measurable (index : Nat) :
    (Space.product parameter (Space.pi fun _ : Fin ambient => borel)).Measurable
      (fun pair => family.Selected index pair.1 pair.2) :=
  (Space.product parameter _).inter (family.chart index).member_measurable
    ((Space.product parameter _).iInter fun other =>
      implies_measurable (family.chart other).member_measurable (family.Before index other))

/-- At most one stratum is selected for a point. -/
public theorem Family.selected_unique {first second : Nat} {θ : Θ} {point : Fin ambient → Carrier}
    (firstSelected : family.Selected first θ point)
    (secondSelected : family.Selected second θ point) : first = second := by
  have forward := firstSelected.2 second secondSelected.1
  have backward := secondSelected.2 first firstSelected.1
  unfold Family.Before at forward backward
  omega

private theorem exists_least {property : Nat → Prop} (start : Nat) (holds : property start) :
    ∃ least, property least ∧ ∀ other, property other → least ≤ other := by
  classical
  induction start using Nat.strongRecOn with
  | ind start earlier =>
      by_cases below : ∃ other, property other ∧ other < start
      · rcases below with ⟨other, otherHolds, less⟩
        exact earlier other less otherHolds
      · refine ⟨start, holds, fun other otherHolds => ?_⟩
        exact Nat.le_of_not_lt fun less => below ⟨other, otherHolds, less⟩

/-- A point in some chart's image has a selected stratum. -/
public theorem Family.exists_selected {index : Nat} {θ : Θ} {point : Fin ambient → Carrier}
    (member : (family.chart index).member θ point) : ∃ selected, family.Selected selected θ point := by
  rcases exists_least (property := fun level =>
      ∃ other, (family.chart other).member θ point ∧ family.dimension other = level)
      _ ⟨index, member, rfl⟩ with ⟨level, ⟨witness, witnessMember, witnessLevel⟩, lowest⟩
  rcases exists_least (property := fun other =>
      (family.chart other).member θ point ∧ family.dimension other = level)
      witness ⟨witnessMember, witnessLevel⟩ with ⟨selected, ⟨selectedMember, selectedLevel⟩, least⟩
  refine ⟨selected, selectedMember, fun other otherMember => ?_⟩
  have atLeast := lowest _ ⟨other, otherMember, rfl⟩
  unfold Family.Before
  by_cases same : family.dimension other = level
  · exact Or.inr ⟨selectedLevel.trans same.symm, least other ⟨otherMember, same⟩⟩
  · exact Or.inl (by omega)

end

end Problib.Measure.Kernel.Chart
