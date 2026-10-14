module

public import Problib.Measure.Kernel.Hahn.Basic
public import Problib.Measure.Decomposition.Hahn.Countable
public import Problib.Measure.Decomposition.Hahn.Existence
import Problib.Measure.Space.Selection
import Problib.Measure.Product.Selection

set_option autoImplicit false

/-!
# Hahn decomposition for kernels with countably generated target

Constructs a jointly measurable Hahn decomposition for transition kernels with
finite fibers targeting a countably generated space. Approximating algebra sets
are chosen through countable selection to form the deterministic defect limit.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

namespace Hahn

/-- Measurability of the fiberwise Hahn score across inputs for a fixed target region. -/
public theorem score_measurable (left right : Kernel source target) {region : Set β}
    (measurable : target.Measurable region) :
    ENNRealMeasurable source (fun input => Measure.Hahn.score (left input) (right input) region) :=
  (left.measurable measurable).add (right.measurable (target.complement measurable))

/-- Input measurability of the supremum Hahn score over a countable generating algebra. -/
public theorem supremum_measurable (algebra : Space.CountableAlgebra target)
    (left right : Kernel source target)
    (leftFinite : ∀ input, Measure.IsFinite (left input))
    (rightFinite : ∀ input, Measure.IsFinite (right input)) :
    ENNRealMeasurable source (fun input => Measure.Hahn.supremum (left input) (right input)) := by
  have equal : (fun input => Measure.Hahn.supremum (left input) (right input)) =
      (fun input => ENNReal.iSup (fun index =>
        Measure.Hahn.score (left input) (right input) (algebra.sets index))) := by
    funext input
    exact Measure.Hahn.supremum_eq_iSup algebra (leftFinite input) (rightFinite input)
  rw [equal]
  exact ENNRealMeasurable.iSup (fun index =>
    score_measurable left right (algebra.toCountableGenerator.measurable index))

/-- Input measurability of the Hahn defect from supremum score for a fixed target region. -/
public theorem defect_measurable (algebra : Space.CountableAlgebra target)
    (left right : Kernel source target)
    (leftFinite : ∀ input, Measure.IsFinite (left input))
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    {region : Set β} (measurable : target.Measurable region) :
    ENNRealMeasurable source (fun input => Measure.Hahn.defect (left input) (right input) region) :=
  (supremum_measurable algebra left right leftFinite rightFinite).sub
    (score_measurable left right measurable)

/-- Constructs a product-measurable family of sets approximating the supremum Hahn score
within an arbitrary positive error bound across all fibers through countable selection. -/
public theorem exists_approximation (algebra : Space.CountableAlgebra target)
    (left right : Kernel source target)
    (leftFinite : ∀ input, Measure.IsFinite (left input))
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    {error : ENNReal} (positive : ENNReal.lt ENNReal.zero error) :
    ∃ region : α → Set β,
      (Space.product source target).Measurable (fun pair => region pair.1 pair.2) ∧
      ∀ input, ENNReal.le (Measure.Hahn.defect (left input) (right input) (region input)) error := by
  let sets : Nat → Set α := fun index input =>
    ENNReal.le (Measure.Hahn.defect (left input) (right input) (algebra.sets index)) error
  have measurable : ∀ index, source.Measurable (sets index) :=
    fun index => (defect_measurable algebra left right leftFinite rightFinite
      (algebra.toCountableGenerator.measurable index)).iic error
  have covered : ∀ input, ∃ index, sets index input :=
    fun input => Measure.Hahn.exists_index_defect_le algebra (leftFinite input) (rightFinite input) positive
  rcases source.exists_measurable_selection sets measurable covered with
    ⟨selection, selectionMeasurable, selected⟩
  exact ⟨fun input => algebra.sets (selection input),
    Space.selected_set_measurable selectionMeasurable algebra.sets algebra.toCountableGenerator.measurable,
    selected⟩

end Hahn

/-- Existence of a jointly measurable Hahn decomposition for kernels with finite fibers
targeting a countably generated space. -/
public theorem exists_hahnDecomposition_of_countableGenerator
    (generator : Space.CountableGenerator target) {left right : Kernel source target}
    (leftFinite : ∀ input, Measure.IsFinite (left input))
    (rightFinite : ∀ input, Measure.IsFinite (right input)) :
    Nonempty (HahnDecomposition left right) := by
  classical
  rcases ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive with
    ⟨errors, positive, summable⟩
  have errorsFinite : ENNReal.Finite (ENNReal.tsum errors) :=
    ENNReal.finite_of_le summable True.intro
  have choices := fun index => Hahn.exists_approximation generator.algebra left right leftFinite
    rightFinite (positive index)
  let sets : Nat → α → Set β := fun index => Classical.choose (choices index)
  have properties := fun index => Classical.choose_spec (choices index)
  let region : α → Set β := fun input => Measure.Hahn.limitSet (fun index => sets index input)
  have measurable : (Space.product source target).Measurable (fun pair => region pair.1 pair.2) :=
    Measure.Hahn.limitSet_measurable (fun index (pair : α × β) => sets index pair.1 pair.2)
      (fun index => (properties index).1)
  have fiberMeasurable (input : α) : target.Measurable (region input) :=
    (Space.pair_measurable (MeasurableMap.constant target source input)
      (MeasurableMap.identity target)) measurable
  have maximal (input : α) : ∀ other, target.Measurable other →
      ENNReal.le (Measure.Hahn.score (left input) (right input) other)
        (Measure.Hahn.score (left input) (right input) (region input)) := by
    intro other otherMeasurable
    exact Measure.Hahn.score_le_limitSet (leftFinite input) (rightFinite input)
      (fun index => sets index input)
      (fun index => (Space.pair_measurable (MeasurableMap.constant target source input)
        (MeasurableMap.identity target)) (properties index).1)
      errors errorsFinite (fun index => (properties index).2 input) otherMeasurable
  let fibers := fun input => Measure.HahnDecomposition.ofMaximal (leftFinite input) (rightFinite input)
    (region input) (fiberMeasurable input) (maximal input)
  exact ⟨{
    region := region
    measurable := measurable
    positive := fun input => (fibers input).positive
    negative := fun input => (fibers input).negative
  }⟩

/-- Chooses a jointly measurable Hahn decomposition for kernels with finite fibers
targeting a countably generated space by defect-limit maximization. -/
public noncomputable def HahnDecomposition.ofCountableGenerator
    (generator : Space.CountableGenerator target) {left right : Kernel source target}
    (leftFinite : ∀ input, Measure.IsFinite (left input))
    (rightFinite : ∀ input, Measure.IsFinite (right input)) : HahnDecomposition left right :=
  Classical.choice (exists_hahnDecomposition_of_countableGenerator generator leftFinite rightFinite)

end Problib.Measure.Kernel
