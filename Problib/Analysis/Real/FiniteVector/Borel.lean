module

public import Problib.Analysis.Real.FiniteVector.Basis
public import Problib.Measure.Pi
public import Problib.Measure.Real.Borel

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Measure
open Problib.Real.Construction.Dedekind

/-- The finite coordinate product of Problib's real Borel space. -/
@[expose] public def vectorBorel (dimension : Nat) : Space (carrier dimension) :=
  Space.pi (fun _ : Fin dimension => Problib.Measure.Real.borel)

private def coordinateBox {dimension : Nat} (lower upper : carrier dimension)
    (index : Nat) : Set (carrier dimension) :=
  if inside : index < dimension then
    fun point => le (lower ⟨index, inside⟩) (point ⟨index, inside⟩) ∧
      le (point ⟨index, inside⟩) (upper ⟨index, inside⟩)
  else Set.univ

private theorem coordinateBox_measurable {dimension : Nat}
    (lower upper : carrier dimension) (index : Nat) :
    (vectorBorel dimension).Measurable (coordinateBox lower upper index) := by
  classical
  unfold coordinateBox
  split
  next inside =>
    apply (vectorBorel dimension).inter
    · exact (Space.coordinate_measurable
        (fun _ : Fin dimension => Problib.Measure.Real.borel)
        ⟨index, inside⟩) (Problib.Measure.Real.measurable_ici _)
    · exact (Space.coordinate_measurable
        (fun _ : Fin dimension => Problib.Measure.Real.borel)
        ⟨index, inside⟩) (Problib.Measure.Real.measurable_iic _)
  next outside => exact (vectorBorel dimension).univ

public theorem closedBox_measurable {dimension : Nat}
    (lower upper : carrier dimension) :
    (vectorBorel dimension).Measurable (closedBox lower upper) := by
  have all := (vectorBorel dimension).iInter
    (coordinateBox_measurable lower upper)
  have equal : closedBox lower upper =
      Set.iInter (coordinateBox lower upper) := by
    apply Set.ext
    intro point
    constructor
    · intro inBox index
      by_cases inside : index < dimension
      · simp only [coordinateBox, dif_pos inside]
        exact inBox ⟨index, inside⟩
      · simp only [coordinateBox, dif_neg inside, Set.univ]
    · intro inAll coordinate
      have included := inAll coordinate.val
      simpa only [coordinateBox, dif_pos coordinate.isLt] using included
  rw [equal]
  exact all

/-- A Euclidean open set is measurable in the finite product Borel space.
The rational closed boxes form a countable cover subordinate to the open set. -/
public theorem open_measurable {dimension : Nat}
    {region : Set (carrier dimension)} (openRegion : IsOpen region) :
    (vectorBorel dimension).Measurable region := by
  classical
  let box (code : Nat) : Set (carrier dimension) :=
    closedBox
      (rationalCenter dimension (Problib.Countable.Pair.decode code).1)
      (rationalCenter dimension (Problib.Countable.Pair.decode code).2)
  let selected (code : Nat) : Set (carrier dimension) :=
    if Set.Subset (box code) region then box code else Set.empty
  have each (code : Nat) : (vectorBorel dimension).Measurable
      (selected code) := by
    unfold selected
    split
    · exact closedBox_measurable _ _
    · exact (vectorBorel dimension).empty
  have cover : region = Set.iUnion selected := by
    apply Set.ext
    intro point
    constructor
    · intro member
      rcases exists_rational_closedBox_inside openRegion member with
        ⟨lowerCode, upperCode, inBox, boxInside⟩
      let code := Problib.Countable.Pair.encode (lowerCode, upperCode)
      refine ⟨code, ?_⟩
      have corner : Problib.Countable.Pair.decode code =
          (lowerCode, upperCode) :=
        Problib.Countable.Pair.decode_encode _
      have boxEqual : box code = closedBox
          (rationalCenter dimension lowerCode)
          (rationalCenter dimension upperCode) := by
        simp only [box, corner]
      change selected code point
      simp only [selected, if_pos (boxEqual ▸ boxInside), boxEqual]
      exact inBox
    · rintro ⟨code, inSelected⟩
      by_cases included : Set.Subset (box code) region
      · exact included (by simpa only [selected, if_pos included] using inSelected)
      · simp only [selected, if_neg included, Set.empty] at inSelected
  rw [cover]
  exact (vectorBorel dimension).iUnion each

end Problib.Analysis.Real.FiniteVector
