import Foundations.Power
import Foundations.Probability.Finite.Distribution
import Foundations.Probability.Finite.Product

namespace Foundations.Probability

universe u v

open Foundations

namespace FiniteDistribution

noncomputable def independent {α : Type u} :
    {n : Nat} → Power (FiniteDistribution α) n → FiniteDistribution (Power α n)
  | 0, .nil => pure .nil
  | _ + 1, .cons head tail =>
      bind head fun value => map (Power.cons value) (independent tail)

theorem independent_cons {α : Type u} {n : Nat}
    (head : FiniteDistribution α) (tail : Power (FiniteDistribution α) n) :
    independent (Power.cons head tail) =
      bind head fun value => bind (independent tail) fun rest =>
        pure (Power.cons value rest) := by
  change bind head (fun value => map (Power.cons value) (independent tail)) = _
  apply bind_congr
  intro value
  exact map_eq_bind_pure (Power.cons value) (independent tail)

theorem independent_pure {α : Type u} {n : Nat} (values : Power α n) :
    independent (Power.map pure values) = pure values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change bind (pure head) (fun value =>
        map (Power.cons value) (independent (Power.map pure tail))) =
          pure (Power.cons head tail)
      rw [bind_pure_left, ih, map_pure]

theorem independent_replicate_pure {α : Type u} (value : α) (n : Nat) :
    independent (Power.replicate (pure value) n) =
      pure (Power.replicate value n) := by
  rw [← Power.map_replicate]
  exact independent_pure (Power.replicate value n)

theorem independent_bind {α : Type u} {β : Type v} {n : Nat}
    (laws : Power (FiniteDistribution α) n)
    (kernels : Power (α → FiniteDistribution β) n) :
    independent (Power.zipWith bind laws kernels) =
      bind (independent laws) fun values =>
        independent (Power.zipWith (fun kernel value => kernel value) kernels values) := by
  induction laws with
  | nil =>
      cases kernels
      change pure (Power.nil : Power β 0) =
        bind (pure (Power.nil : Power α 0)) fun _ =>
          pure (Power.nil : Power β 0)
      rw [bind_pure_left]
  | cons head tail ih =>
      cases kernels with
      | cons kernel rest =>
          simp only [Power.zipWith, independent_cons, ih, bind_assoc, bind_pure_left]
          apply bind_congr
          intro sourceValue
          let continuation := fun result restValues =>
            bind (independent (Power.zipWith
              (fun nextKernel value => nextKernel value) rest restValues)) fun restResult =>
                pure (Power.cons result restResult)
          exact bind_commute (kernel sourceValue) (independent tail) continuation

theorem independent_map {α : Type u} {β : Type v} {n : Nat}
    (transforms : Power (α → β) n) (laws : Power (FiniteDistribution α) n) :
    independent (Power.zipWith (fun transform law => map transform law)
      transforms laws) =
      map (fun values => Power.zipWith (fun transform value => transform value)
        transforms values) (independent laws) := by
  induction laws with
  | nil =>
      cases transforms
      change pure (Power.nil : Power β 0) =
        map (fun _ => (Power.nil : Power β 0))
          (pure (Power.nil : Power α 0))
      rw [map_pure]
  | cons head tail ih =>
      cases transforms with
      | cons transform rest =>
          change independent (Power.cons (map transform head)
              (Power.zipWith (fun nextTransform law => map nextTransform law)
                rest tail)) =
            map (fun values => Power.zipWith
              (fun nextTransform nextValue => nextTransform nextValue)
              (Power.cons transform rest) values)
              (independent (Power.cons head tail))
          rw [independent_cons, bind_map_left]
          calc
            bind head (fun value =>
                bind (independent (Power.zipWith
                  (fun nextTransform law => map nextTransform law) rest tail))
                  fun restResult => pure (Power.cons (transform value) restResult)) =
                bind head (fun value => bind (independent tail) fun restValues =>
                  pure (Power.cons (transform value)
                    (Power.zipWith (fun nextTransform nextValue =>
                      nextTransform nextValue) rest restValues))) := by
              apply bind_congr
              intro value
              rw [ih rest, bind_map_left]
            _ = map (fun values => Power.zipWith
                (fun nextTransform nextValue => nextTransform nextValue)
                (Power.cons transform rest) values)
                (independent (Power.cons head tail)) := by
              rw [independent_cons, ← bind_map_right]
              apply bind_congr
              intro value
              rw [← bind_map_right]
              apply bind_congr
              intro restValues
              rw [map_pure]
              rfl

theorem independent_map_same {α : Type u} {β : Type v} {n : Nat}
    (transform : α → β) (laws : Power (FiniteDistribution α) n) :
    independent (Power.map (map transform) laws) =
      map (Power.map transform) (independent laws) := by
  have mappedLaws :
      Power.zipWith (fun nextTransform law => map nextTransform law)
          (Power.replicate transform n) laws =
        Power.map (map transform) laws := by
    induction laws with
    | nil => rfl
    | cons head tail induction =>
        simp [Power.map, Power.zipWith, Power.replicate, induction]
  rw [← mappedLaws]
  calc
    independent (Power.zipWith (fun nextTransform law => map nextTransform law)
        (Power.replicate transform n) laws) =
      map (fun values => Power.zipWith
        (fun nextTransform value => nextTransform value)
        (Power.replicate transform n) values) (independent laws) :=
      independent_map (Power.replicate transform n) laws
    _ = map (Power.map transform) (independent laws) := by
      apply congrArg (fun nextTransform => map nextTransform (independent laws))
      funext values
      exact Power.zipWith_replicate_left transform values

theorem independent_bind_pair {α : Type u} {β : Type v} {n : Nat}
    (laws : Power (FiniteDistribution α) n)
    (kernels : Power (α → FiniteDistribution β) n) :
    independent (Power.zipWith (fun law kernel => bind law fun value =>
      map (fun result => (value, result)) (kernel value)) laws kernels) =
      bind (independent laws) fun values =>
        map (Power.combine values)
          (independent (Power.zipWith (fun kernel value => kernel value)
            kernels values)) := by
  let pairedKernels := Power.map (fun kernel value =>
    map (fun result => (value, result)) (kernel value)) kernels
  have componentEqual :
      Power.zipWith (fun law kernel => bind law fun value =>
          map (fun result => (value, result)) (kernel value)) laws kernels =
        Power.zipWith bind laws pairedKernels := by
    induction laws with
    | nil =>
        cases kernels
        rfl
    | cons head tail ih =>
        cases kernels with
        | cons kernel rest => simp [pairedKernels, Power.map, Power.zipWith, ih]
  have applicationsEqual : ∀ values,
      Power.zipWith (fun kernel value => kernel value) pairedKernels values =
        Power.zipWith (fun transform law => map transform law)
          (Power.map (fun value result => (value, result)) values)
          (Power.zipWith (fun kernel value => kernel value) kernels values) := by
    intro values
    dsimp [pairedKernels]
    simpa only [Power.zipWith_map_left] using
      (Power.zipWith_map_dependent_apply
        (fun value law => map (fun result => (value, result)) law) kernels values)
  calc
    independent (Power.zipWith (fun law kernel => bind law fun value =>
        map (fun result => (value, result)) (kernel value)) laws kernels) =
        independent (Power.zipWith bind laws pairedKernels) :=
      congrArg independent componentEqual
    _ = bind (independent laws) fun values =>
        independent (Power.zipWith (fun kernel value => kernel value)
          pairedKernels values) := independent_bind laws pairedKernels
    _ = bind (independent laws) fun values =>
        map (Power.combine values)
          (independent (Power.zipWith (fun kernel value => kernel value)
            kernels values)) := by
      apply bind_congr
      intro values
      rw [applicationsEqual]
      simpa [Power.zipWith_map_left, Power.zipWith_pair_eq_combine] using
        (independent_map (Power.map (fun value result => (value, result)) values)
          (Power.zipWith (fun kernel value => kernel value) kernels values))

end FiniteDistribution

structure DensityComponent (α : Type u) [DecidableEq α] where
  measure : FiniteMeasure α
  reference : FiniteMeasure α
  density : α → NNRat
  correct : FiniteMeasure.IsDensity measure reference density

namespace DensityComponent

def independentMeasure {α : Type u} [DecidableEq α] :
    (components : List (DensityComponent α)) → FiniteMeasure (Power α components.length)
  | [] => FiniteMeasure.dirac .nil
  | head :: tail =>
      FiniteMeasure.map Power.fromPair
        (FiniteMeasure.product head.measure (independentMeasure tail))

def independentReference {α : Type u} [DecidableEq α] :
    (components : List (DensityComponent α)) → FiniteMeasure (Power α components.length)
  | [] => FiniteMeasure.dirac .nil
  | head :: tail =>
      FiniteMeasure.map Power.fromPair
        (FiniteMeasure.product head.reference (independentReference tail))

def independentDensity {α : Type u} [DecidableEq α] :
    (components : List (DensityComponent α)) → Power α components.length → NNRat
  | [], .nil => 1
  | head :: tail, .cons value rest => head.density value * independentDensity tail rest

theorem independent_isDensity {α : Type u} [DecidableEq α]
    (components : List (DensityComponent α)) :
    FiniteMeasure.IsDensity (independentMeasure components)
      (independentReference components) (independentDensity components) := by
  induction components with
  | nil =>
      intro point
      cases point
      simp [independentMeasure, independentReference, independentDensity,
        FiniteMeasure.mass_dirac]
  | cons head tail ih =>
      have productCorrect := FiniteMeasure.product_isDensity head.correct ih
      have mappedCorrect :=
        FiniteMeasure.map_isDensity_of_bijection productCorrect Power.fromPair Power.toPair
          Power.toPair_fromPair Power.fromPair_toPair
      intro point
      simp only [independentMeasure, independentReference]
      rw [mappedCorrect point]
      cases point
      rfl

end DensityComponent

end Foundations.Probability
