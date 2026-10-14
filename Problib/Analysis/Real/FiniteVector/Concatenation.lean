module

public import Problib.Analysis.Real.FiniteVector.Borel
public import Problib.Measure.Product

/-! Concatenation of finite vectors and its two projections. Each is
measurable for the coordinate Borel spaces, so Lebesgue measure and PAP maps
can both be stated on concatenated coordinates. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Measure

/-- Concatenate finite vectors without changing either coordinate block. -/
@[expose] public def pairVector {left right : Nat}
    (first : carrier left) (second : carrier right) : carrier (left + right) :=
  fun coordinate => Fin.addCases (fun index => first index)
    (fun index => second index) coordinate

/-- The first block of a concatenated vector. -/
@[expose] public def leftVector {left right : Nat} :
    carrier (left + right) → carrier left :=
  fun vector coordinate => vector (Fin.castAdd right coordinate)

/-- The second block of a concatenated vector. -/
@[expose] public def rightVector {left right : Nat} :
    carrier (left + right) → carrier right :=
  fun vector coordinate => vector (Fin.natAdd left coordinate)

@[simp] public theorem leftVector_pairVector {left right : Nat}
    (first : carrier left) (second : carrier right) :
    leftVector (pairVector first second) = first := by
  funext coordinate
  simp only [leftVector, pairVector, Fin.addCases_left]

@[simp] public theorem rightVector_pairVector {left right : Nat}
    (first : carrier left) (second : carrier right) :
    rightVector (pairVector first second) = second := by
  funext coordinate
  simp only [rightVector, pairVector, Fin.addCases_right]

@[simp] public theorem pairVector_left_right {left right : Nat}
    (vector : carrier (left + right)) :
    pairVector (leftVector vector) (rightVector vector) = vector := by
  funext coordinate
  refine Fin.addCases (fun index => ?_) (fun index => ?_) coordinate
  · simp only [pairVector, leftVector, Fin.addCases_left]
  · simp only [pairVector, rightVector, Fin.addCases_right]

/-- Concatenation is measurable on the product of the two blocks' Borel
spaces. -/
public theorem pairVector_measurable (left right : Nat) :
    MeasurableMap (Space.product (vectorBorel left) (vectorBorel right))
      (vectorBorel (left + right)) (fun pair => pairVector pair.1 pair.2) := by
  apply Space.pi_measurable
  intro coordinate
  refine Fin.addCases (fun index => ?_) (fun index => ?_) coordinate
  · have equal : (fun pair : carrier left × carrier right =>
        pairVector pair.1 pair.2 (Fin.castAdd right index)) =
        fun pair => pair.1 index := by
      funext pair
      simp only [pairVector, Fin.addCases_left]
    rw [equal]
    exact MeasurableMap.comp
      (Space.coordinate_measurable (fun _ : Fin left => Problib.Measure.Real.borel) index)
      (Space.first_measurable _ _)
  · have equal : (fun pair : carrier left × carrier right =>
        pairVector pair.1 pair.2 (Fin.natAdd left index)) =
        fun pair => pair.2 index := by
      funext pair
      simp only [pairVector, Fin.addCases_right]
    rw [equal]
    exact MeasurableMap.comp
      (Space.coordinate_measurable (fun _ : Fin right => Problib.Measure.Real.borel) index)
      (Space.second_measurable _ _)

public theorem leftVector_measurable (left right : Nat) :
    MeasurableMap (vectorBorel (left + right)) (vectorBorel left)
      (leftVector (left := left) (right := right)) :=
  Space.pi_measurable fun coordinate =>
    Space.coordinate_measurable (fun _ : Fin (left + right) => Problib.Measure.Real.borel)
      (Fin.castAdd right coordinate)

public theorem rightVector_measurable (left right : Nat) :
    MeasurableMap (vectorBorel (left + right)) (vectorBorel right)
      (rightVector (left := left) (right := right)) :=
  Space.pi_measurable fun coordinate =>
    Space.coordinate_measurable (fun _ : Fin (left + right) => Problib.Measure.Real.borel)
      (Fin.natAdd left coordinate)

end Problib.Analysis.Real.FiniteVector
