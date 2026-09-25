module

public import Problib.Analysis.PAP.Gluing

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

/-- The unique partition index at a point of a represented domain. -/
public noncomputable def PAPRepresentation.pieceIndex {source target : Nat}
    {domain : Problib.Measure.Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    (point : carrier source) (member : domain point) : Nat :=
  Classical.choose (representation.cover ▸ member)

public theorem PAPRepresentation.pieceIndex_eq {source target : Nat}
    {domain : Problib.Measure.Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    (index : Nat) (point : carrier source)
    (member : representation.pieces index point)
    (inDomain : domain point) :
    representation.pieceIndex point inDomain = index := by
  have chosenMember : representation.pieces
      (representation.pieceIndex point inDomain) point :=
    Classical.choose_spec (representation.cover ▸ inDomain)
  by_cases equal : representation.pieceIndex point inDomain = index
  · exact equal
  · exact False.elim
      (representation.pairwise _ _ equal chosenMember member)

/-- The Jacobian chosen by a PAP representation. On a partition piece it
differentiates that piece's analytic witness, coordinate by coordinate. Its
value outside the represented domain is zero. -/
@[expose] public noncomputable def PAPRepresentation.intensionalDerivative
    {source target : Nat} {domain : Problib.Measure.Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    (point : carrier source) : Fin source → carrier target := by
  classical
  exact if member : domain point then
    let piece := representation.pieceIndex point member
    fun input output => partialDerivativeAt
      (fun nearby => representation.witnesses piece nearby output) point input
  else fun _ => zeroVector target

/-- On every partition piece, the chosen Jacobian is the coordinate
derivative of that piece's analytic witness. -/
public theorem PAPRepresentation.intensionalDerivative_on_piece
    {source target : Nat} {domain : Problib.Measure.Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    (index : Nat) (point : carrier source)
    (member : representation.pieces index point)
    (input : Fin source) (output : Fin target) :
    representation.intensionalDerivative point input output =
      partialDerivativeAt
        (fun nearby => representation.witnesses index nearby output)
        point input := by
  classical
  have inDomain : domain point := by
    rw [representation.cover]
    exact ⟨index, member⟩
  unfold PAPRepresentation.intensionalDerivative
  simp only [dif_pos inDomain]
  rw [representation.pieceIndex_eq index point member inDomain]

/-- The partial map's derivative retains its chosen representation. -/
@[expose] public noncomputable def PartialPAP.intensionalDerivative
    {source target : Nat} (map : PartialPAP source target)
    (point : carrier source) : Fin source → carrier target :=
  map.representation.intensionalDerivative point

end Problib.Analysis.PAP
