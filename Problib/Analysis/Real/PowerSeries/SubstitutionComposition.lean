module

public import Problib.Analysis.Real.PowerSeries.SubstitutionCenter

/-! Analytic composition follows from normally convergent substitution after
centering each inner coordinate series at the image of the source center. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

public theorem ball_subvector_iff {dimension : Nat}
    (center point : FiniteVector.carrier dimension)
    (radius : selection.Carrier) :
    FiniteVector.ball center radius point ↔
      FiniteVector.ball (FiniteVector.zeroVector dimension) radius
        (FiniteVector.subVector point center) := by
  constructor
  · intro inside coordinate
    change lt (abs (sub
      (sub (point coordinate) (center coordinate)) zero)) radius
    rw [sub_zero]
    exact inside coordinate
  · intro inside coordinate
    have near := inside coordinate
    change lt (abs (sub
      (sub (point coordinate) (center coordinate)) zero)) radius
      at near
    rwa [sub_zero] at near

public theorem analytic_vector_preimage_open {source target : Nat}
    {innerRegion : FiniteVector.carrier source → Prop}
    {outerRegion : FiniteVector.carrier target → Prop}
    {inner : FiniteVector.carrier source → FiniteVector.carrier target}
    (innerOpen : FiniteVector.IsOpen innerRegion)
    (outerOpen : FiniteVector.IsOpen outerRegion)
    (innerAnalytic : AnalyticVectorOn innerRegion inner) :
    FiniteVector.IsOpen
      (fun point => innerRegion point ∧ outerRegion (inner point)) := by
  intro center member
  rcases innerOpen center member.left with
    ⟨innerRadius, innerPositive, innerWithin⟩
  rcases outerOpen (inner center) member.right with
    ⟨outerRadius, outerPositive, outerWithin⟩
  rcases analytic_vector_continuous_at innerAnalytic center member.left
    outerRadius outerPositive with
    ⟨continuityRadius, continuityPositive, innerNear⟩
  rcases small_positive innerPositive continuityPositive with
    ⟨radius, positive, belowInner, belowContinuity⟩
  refine ⟨radius, positive, fun point inside => ?_⟩
  exact ⟨innerWithin point (FiniteVector.ball_mono belowInner inside),
    outerWithin (inner point)
      (innerNear point (FiniteVector.ball_mono belowContinuity inside))⟩

public theorem centered_inner_value {source target : Nat}
    (inner : FiniteVector.carrier source → FiniteVector.carrier target)
    (center : FiniteVector.carrier source)
    (series : Fin target → Convergent source)
    (agrees : ∀ coordinate point
      (inside : FiniteVector.ball center
        (series coordinate).radius point),
      inner point coordinate =
        value (series coordinate) (FiniteVector.subVector point center)
          (by
            intro index
            simpa only [FiniteVector.ball, FiniteVector.zeroVector,
              FiniteVector.subVector, sub_zero] using inside index))
    (radius : selection.Carrier)
    (below : ∀ coordinate,
      le radius (centerSeries (series coordinate)).radius)
    (point : FiniteVector.carrier source)
    (inside : FiniteVector.ball center radius point) :
    innerValuePoint (fun coordinate => centerSeries (series coordinate))
      radius below (FiniteVector.subVector point center)
      ((ball_subvector_iff center point radius).mp inside) =
    FiniteVector.subVector (inner point) (inner center) := by
  funext coordinate
  have originalInside : FiniteVector.ball center
      (series coordinate).radius point := by
    intro index
    have near := FiniteVector.ball_mono
      (below coordinate)
      ((ball_subvector_iff center point radius).mp inside)
    have bound := near index
    change lt (abs (sub
      (sub (point index) (center index)) zero))
      (series coordinate).radius at bound
    rwa [sub_zero] at bound
  exact centered_local_value (series coordinate) center
    (fun point => inner point coordinate) (agrees coordinate)
    point originalInside

public theorem analytic_on_comp {source target : Nat}
    {innerRegion : FiniteVector.carrier source → Prop}
    {outerRegion : FiniteVector.carrier target → Prop}
    {inner : FiniteVector.carrier source → FiniteVector.carrier target}
    {outer : FiniteVector.carrier target → selection.Carrier}
    (innerOpen : FiniteVector.IsOpen innerRegion)
    (innerAnalytic : AnalyticVectorOn innerRegion inner)
    (outerAnalytic : AnalyticOn outerRegion outer)
    (maps : ∀ point, innerRegion point → outerRegion (inner point)) :
    AnalyticOn innerRegion (fun point => outer (inner point)) := by
  refine ⟨innerOpen, fun center member => ?_⟩
  rcases outerAnalytic.right (inner center) (maps center member) with
    ⟨outerSeries, _, outerAgree⟩
  let witness := fun coordinate : Fin target =>
    (innerAnalytic coordinate).right center member
  let series : Fin target → Convergent source :=
    fun coordinate => Classical.choose (witness coordinate)
  have agrees : ∀ coordinate point
      (inside : FiniteVector.ball center
        (series coordinate).radius point),
      inner point coordinate =
        value (series coordinate) (FiniteVector.subVector point center)
          ((ball_subvector_iff center point
            (series coordinate).radius).mp inside) := by
    intro coordinate point inside
    exact (Classical.choose_spec (witness coordinate)).2 point inside
  let centered : Fin target → Convergent source :=
    fun coordinate => centerSeries (series coordinate)
  have zeroConstant : ∀ coordinate,
      (centered coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero := by
    intro coordinate
    exact centerSeries_zero_constant (series coordinate)
  rcases substitution_common_radius outerSeries centered zeroConstant with
    ⟨substitutionRadius, substitutionPositive, below, outerInside⟩
  rcases innerOpen center member with
    ⟨domainRadius, domainPositive, domainWithin⟩
  rcases small_positive substitutionPositive domainPositive with
    ⟨radius, positive, belowSubstitution, belowDomain⟩
  let composite := substituteSeriesWithin outerSeries centered
    substitutionRadius substitutionPositive below zeroConstant outerInside
  let localSeries := restrictRadius composite radius positive belowSubstitution
  refine ⟨localSeries, ?_, ?_⟩
  · intro point inside
    exact domainWithin point (FiniteVector.ball_mono belowDomain inside)
  · intro point inside
    have substitutionInside : FiniteVector.ball center
        substitutionRadius point :=
      FiniteVector.ball_mono belowSubstitution inside
    let displacement := FiniteVector.subVector point center
    have displacementInside : FiniteVector.ball
        (FiniteVector.zeroVector source) substitutionRadius
        displacement :=
      (ball_subvector_iff center point substitutionRadius).mp
        substitutionInside
    have innerDisplacement :
        innerValuePoint centered substitutionRadius below displacement
          displacementInside =
        FiniteVector.subVector (inner point) (inner center) :=
      centered_inner_value inner center series agrees
        substitutionRadius below point substitutionInside
    have imageInside : FiniteVector.ball
        (inner center) outerSeries.radius (inner point) := by
      have outerPointInside := innerValuePoint_inside_outer
        outerSeries centered substitutionRadius below zeroConstant
        outerInside displacement displacementInside
      intro coordinate
      have near := outerPointInside coordinate
      have equalCoordinate := congrFun innerDisplacement coordinate
      rw [equalCoordinate] at near
      change lt (abs (sub
        (sub (inner point coordinate) (inner center coordinate)) zero))
        outerSeries.radius at near
      rwa [sub_zero] at near
    have substituted := substituteSeriesWithin_value outerSeries
      centered substitutionRadius substitutionPositive below zeroConstant
      outerInside displacement displacementInside
    have substitutedValue : value composite displacement
        displacementInside =
        value outerSeries
          (FiniteVector.subVector (inner point) (inner center))
          ((ball_subvector_iff (inner center) (inner point)
            outerSeries.radius).mp imageInside) := by
      simpa only [composite, innerDisplacement] using substituted
    have originalValue := outerAgree (inner point) imageInside
    have localInside : FiniteVector.ball
        (FiniteVector.zeroVector source) radius displacement :=
      (ball_subvector_iff center point radius).mp inside
    calc
      outer (inner point) =
          value outerSeries
            (FiniteVector.subVector (inner point) (inner center))
            ((ball_subvector_iff (inner center) (inner point)
              outerSeries.radius).mp imageInside) := originalValue
      _ = value composite displacement displacementInside :=
        substitutedValue.symm
      _ = value localSeries displacement localInside :=
        (restrictRadius_value composite radius positive
          belowSubstitution displacement localInside).symm

public theorem analytic_on_comp_preimage {source target : Nat}
    {innerRegion : FiniteVector.carrier source → Prop}
    {outerRegion : FiniteVector.carrier target → Prop}
    {inner : FiniteVector.carrier source → FiniteVector.carrier target}
    {outer : FiniteVector.carrier target → selection.Carrier}
    (innerOpen : FiniteVector.IsOpen innerRegion)
    (innerAnalytic : AnalyticVectorOn innerRegion inner)
    (outerAnalytic : AnalyticOn outerRegion outer) :
    AnalyticOn
      (fun point => innerRegion point ∧ outerRegion (inner point))
      (fun point => outer (inner point)) := by
  have domainOpen := analytic_vector_preimage_open innerOpen
    outerAnalytic.left innerAnalytic
  have restricted : AnalyticVectorOn
      (fun point => innerRegion point ∧ outerRegion (inner point))
      inner := by
    intro coordinate
    exact analytic_on_open_subset (innerAnalytic coordinate)
      domainOpen (fun _ member => member.left)
  exact analytic_on_comp domainOpen restricted outerAnalytic
    (fun _ member => member.right)

end

end Problib.Analysis.Real.PowerSeries
