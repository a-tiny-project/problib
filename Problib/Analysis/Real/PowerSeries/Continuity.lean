module

public import Problib.Analysis.Real.PowerSeries.AnalyticDerivative

/-! Uniform coordinate bounds for analytic series on smaller boxes. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨add_assoc⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

public theorem degreePolynomialBound_nonnegative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) {radius : selection.Carrier}
    (nonnegative : le zero radius) (selected : Fin dimension) :
    le zero (degreePolynomialBound coefficients count radius selected) := by
  unfold degreePolynomialBound
  exact partial_sum_nonnegative
    (fun degreeValue => finiteShellSliceBound_nonnegative
      coefficients (MultiIndex.degreeShell dimension degreeValue)
      nonnegative selected) count

/-- One constant bounds changes in any chosen coordinate on a fixed smaller
box. A finite prefix supplies the large part; the infinite tail has a
Lipschitz constant below one. -/
public theorem coordinate_value_lipschitz_box {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius))
    (selected : Fin dimension) :
    ∃ constant : selection.Carrier, lt zero constant ∧
      ∀ point : FiniteVector.carrier dimension,
      (∀ coordinate,
        le (abs (point coordinate)) (mul ratio radius)) →
      ∀ first second : selection.Carrier,
      le (abs first) (mul ratio radius) →
      le (abs second) (mul ratio radius) →
      ∀ firstInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected first),
      ∀ secondInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected second),
      le (abs (sub
        (value series (replaceCoordinate point selected second)
          secondInside)
        (value series (replaceCoordinate point selected first)
          firstInside)))
        (mul constant (abs (sub second first))) := by
  let shrunk := mul ratio radius
  have shrunkNonnegative := mul_nonnegative ratioNonnegative
    radiusPositive.left
  rcases full_tail_difference_small series ratioNonnegative
    ratioBelowOne radiusPositive insideRadius selected one_positive with
    ⟨stage, tailSmall⟩
  let prefixBound := degreePolynomialBound series.coefficients stage
    shrunk selected
  have prefixNonnegative := degreePolynomialBound_nonnegative
    series.coefficients stage shrunkNonnegative selected
  let constant := add prefixBound one
  have constantPositive : lt zero constant := by
    have raised := add_lt_add_left prefixBound one_positive
    rw [add_zero] at raised
    exact lt_of_le_of_lt prefixNonnegative raised
  refine ⟨constant, constantPositive, fun point coordinates first second
    firstBound secondBound firstInside secondInside => ?_⟩
  have prefixEstimate := degreePolynomial_difference_bound
    series.coefficients stage point shrunkNonnegative coordinates
    selected firstBound secondBound
  have tail := tailSmall stage (Nat.le_refl stage) point coordinates
    first second firstBound secondBound firstInside secondInside
  let firstPoint := replaceCoordinate point selected first
  let secondPoint := replaceCoordinate point selected second
  have firstSplit := value_eq_polynomial_add_tail series firstPoint
    firstInside stage
  have secondSplit := value_eq_polynomial_add_tail series secondPoint
    secondInside stage
  rw [firstSplit, secondSplit]
  have split :
      sub
        (add (degreePolynomial series.coefficients stage secondPoint)
          (fullTailValue series secondPoint secondInside stage))
        (add (degreePolynomial series.coefficients stage firstPoint)
          (fullTailValue series firstPoint firstInside stage)) =
      add
        (sub (degreePolynomial series.coefficients stage secondPoint)
          (degreePolynomial series.coefficients stage firstPoint))
        (sub (fullTailValue series secondPoint secondInside stage)
          (fullTailValue series firstPoint firstInside stage)) := by
    exact add_sub_add_comm _ _ _ _
  rw [split]
  have triangle := abs_add_le
    (sub (degreePolynomial series.coefficients stage secondPoint)
      (degreePolynomial series.coefficients stage firstPoint))
    (sub (fullTailValue series secondPoint secondInside stage)
      (fullTailValue series firstPoint firstInside stage))
  have combined := add_le_add prefixEstimate tail
  have bound := le_trans triangle combined
  change le _ (mul (add prefixBound one) (abs (sub second first)))
  rw [add_mul, one_mul]
  simpa only [one_mul] using bound

@[expose] public def sweepCoordinates {dimension : Nat}
    (source target : FiniteVector.carrier dimension) :
    List (Fin dimension) → FiniteVector.carrier dimension
  | [] => source
  | selected :: rest =>
      replaceCoordinate (sweepCoordinates source target rest)
        selected (target selected)

public theorem sweep_coordinate_choice {dimension : Nat}
    (source target : FiniteVector.carrier dimension)
    (indices : List (Fin dimension)) (coordinate : Fin dimension) :
    sweepCoordinates source target indices coordinate = source coordinate ∨
      sweepCoordinates source target indices coordinate = target coordinate := by
  induction indices with
  | nil => exact Or.inl rfl
  | cons selected rest induction =>
      by_cases same : coordinate = selected
      · subst coordinate
        exact Or.inr (by simp [sweepCoordinates, replaceCoordinate])
      · rcases induction with left | right
        · exact Or.inl (by simpa [sweepCoordinates, replaceCoordinate,
            same] using left)
        · exact Or.inr (by simpa [sweepCoordinates, replaceCoordinate,
            same] using right)

public theorem sweep_coordinate_of_mem {dimension : Nat}
    (source target : FiniteVector.carrier dimension)
    (indices : List (Fin dimension)) (coordinate : Fin dimension)
    (member : coordinate ∈ indices) :
    sweepCoordinates source target indices coordinate = target coordinate := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons selected rest induction =>
      rcases List.mem_cons.mp member with equal | later
      · subst coordinate
        simp [sweepCoordinates, replaceCoordinate]
      · by_cases same : coordinate = selected
        · subst coordinate
          simp [sweepCoordinates, replaceCoordinate]
        · simpa [sweepCoordinates, replaceCoordinate, same]
            using induction later

public theorem sweep_all_coordinates {dimension : Nat}
    (source target : FiniteVector.carrier dimension) :
    sweepCoordinates source target (List.finRange dimension) = target := by
  funext coordinate
  exact sweep_coordinate_of_mem source target
    (List.finRange dimension) coordinate (List.mem_finRange coordinate)

@[expose] public def coordinateBoundSum {dimension : Nat}
    (constants : Fin dimension → selection.Carrier) :
    List (Fin dimension) → selection.Carrier
  | [] => zero
  | selected :: rest =>
      add (constants selected) (coordinateBoundSum constants rest)

public theorem sweep_difference_bound {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (source target : FiniteVector.carrier dimension)
    (constants : Fin dimension → selection.Carrier)
    (delta : selection.Carrier)
    (stepBound : ∀ indices : List (Fin dimension),
      ∀ selected : Fin dimension,
      le (abs (sub
        (function (replaceCoordinate
          (sweepCoordinates source target indices) selected
          (target selected)))
        (function (sweepCoordinates source target indices))))
        (mul (constants selected) delta))
    (indices : List (Fin dimension)) :
    le (abs (sub (function (sweepCoordinates source target indices))
      (function source)))
      (mul (coordinateBoundSum constants indices) delta) := by
  induction indices with
  | nil =>
      change le (abs (sub (function source) (function source)))
        (mul zero delta)
      rw [sub_self, abs_zero, zero_mul]
      exact le_refl zero
  | cons selected rest induction =>
      let middle := sweepCoordinates source target rest
      let next := replaceCoordinate middle selected (target selected)
      have split : sub (function next) (function source) =
          add (sub (function next) (function middle))
            (sub (function middle) (function source)) :=
        (sub_add_sub _ _ _).symm
      change le (abs (sub (function next) (function source)))
        (mul (add (constants selected)
          (coordinateBoundSum constants rest)) delta)
      rw [split, add_mul]
      exact le_trans (abs_add_le _ _)
        (add_le_add (stepBound rest selected) induction)

@[expose] public noncomputable def totalValue {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension) : selection.Carrier := by
  classical
  exact if inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius point then
    value series point inside
  else zero

public theorem totalValue_of_inside {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius point) :
    totalValue series point = value series point inside := by
  classical
  unfold totalValue
  rw [dif_pos inside]

private theorem value_congr {dimension : Nat}
    (series : Convergent dimension)
    {first second : FiniteVector.carrier dimension}
    (equal : first = second)
    (firstInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius first)
    (secondInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius second) :
    value series first firstInside = value series second secondInside := by
  subst second
  rfl

public theorem coordinateBoundSum_nonnegative {dimension : Nat}
    (constants : Fin dimension → selection.Carrier)
    (positive : ∀ coordinate, le zero (constants coordinate))
    (indices : List (Fin dimension)) :
    le zero (coordinateBoundSum constants indices) := by
  induction indices with
  | nil => exact le_refl zero
  | cons selected rest induction =>
      change le zero (add (constants selected)
        (coordinateBoundSum constants rest))
      exact add_nonnegative (positive selected) induction

/-- Normal convergence and the finite coordinate sweep give a joint local
Lipschitz bound on every sufficiently smaller closed box. -/
public theorem value_lipschitz_box {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius)) :
    ∃ constant : selection.Carrier, lt zero constant ∧
      ∀ source target : FiniteVector.carrier dimension,
      (∀ coordinate,
        le (abs (source coordinate)) (mul ratio radius)) →
      (∀ coordinate,
        le (abs (target coordinate)) (mul ratio radius)) →
      le (abs (sub (totalValue series target)
        (totalValue series source)))
        (mul constant
          (FiniteVector.supNorm
            (FiniteVector.subVector target source))) := by
  classical
  let localWitness := fun selected : Fin dimension =>
    coordinate_value_lipschitz_box series ratioNonnegative
      ratioBelowOne radiusPositive insideRadius selected
  let constants : Fin dimension → selection.Carrier :=
    fun selected => Classical.choose (localWitness selected)
  have constantsPositive : ∀ selected, lt zero (constants selected) :=
    fun selected => (Classical.choose_spec (localWitness selected)).1
  let sumConstants := coordinateBoundSum constants
    (List.finRange dimension)
  let constant := add one sumConstants
  have sumNonnegative := coordinateBoundSum_nonnegative constants
    (fun coordinate => (constantsPositive coordinate).left)
    (List.finRange dimension)
  have constantPositive : lt zero constant := by
    have raised := add_lt_add_right sumConstants one_positive
    rw [zero_add] at raised
    exact lt_of_le_of_lt sumNonnegative raised
  refine ⟨constant, constantPositive, fun source target
    sourceBounds targetBounds => ?_⟩
  let delta := FiniteVector.supNorm
    (FiniteVector.subVector target source)
  have deltaNonnegative := FiniteVector.sup_norm_nonnegative
    (FiniteVector.subVector target source)
  have sweptBound : ∀ indices : List (Fin dimension),
      ∀ coordinate,
      le (abs ((sweepCoordinates source target indices) coordinate))
        (mul ratio radius) := by
    intro indices coordinate
    rcases sweep_coordinate_choice source target indices coordinate
      with sourceEqual | targetEqual
    · rw [sourceEqual]
      exact sourceBounds coordinate
    · rw [targetEqual]
      exact targetBounds coordinate
  have stepBound : ∀ indices : List (Fin dimension),
      ∀ selected : Fin dimension,
      le (abs (sub
        (totalValue series (replaceCoordinate
          (sweepCoordinates source target indices) selected
          (target selected)))
        (totalValue series (sweepCoordinates source target indices))))
        (mul (constants selected) delta) := by
    intro indices selected
    let middle := sweepCoordinates source target indices
    let next := replaceCoordinate middle selected (target selected)
    have middleBounds := sweptBound indices
    have nextBounds : ∀ coordinate,
        le (abs (next coordinate)) (mul ratio radius) := by
      intro coordinate
      by_cases same : coordinate = selected
      · subst coordinate
        simpa [next, replaceCoordinate] using
          targetBounds selected
      · simpa [next, replaceCoordinate, same] using
          middleBounds coordinate
    have middleInside := closed_box_inside series selected
      ratioBelowOne radiusPositive insideRadius middle middleBounds
    have nextInside := closed_box_inside series selected
      ratioBelowOne radiusPositive insideRadius next nextBounds
    have firstInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate middle selected (middle selected)) := by
      rw [replaceCoordinate_at_point]
      exact middleInside
    have localBound := (Classical.choose_spec (localWitness selected)).2
      middle middleBounds (middle selected) (target selected)
      (middleBounds selected) (targetBounds selected)
      firstInside nextInside
    have firstValueEqual : value series
        (replaceCoordinate middle selected (middle selected))
        firstInside = totalValue series middle := by
      rw [totalValue_of_inside series middle middleInside]
      exact value_congr series
        (replaceCoordinate_at_point middle selected)
        firstInside middleInside
    rw [firstValueEqual,
      ← totalValue_of_inside series next nextInside] at localBound
    have differenceBound : le (abs (sub (target selected)
        (middle selected))) delta := by
      change le (abs (sub (target selected)
        (sweepCoordinates source target indices selected))) delta
      rcases sweep_coordinate_choice source target indices selected
        with sourceEqual | targetEqual
      · rw [sourceEqual]
        simpa only [delta, FiniteVector.subVector] using
          FiniteVector.coordinate_le_sup_norm
            (FiniteVector.subVector target source) selected
      · rw [targetEqual, sub_self, abs_zero]
        exact deltaNonnegative
    have scaled := mul_le_mul_nonnegative_left differenceBound
      (constantsPositive selected).left
    exact le_trans localBound scaled
  have path := sweep_difference_bound (totalValue series) source target
    constants delta stepBound (List.finRange dimension)
  rw [sweep_all_coordinates] at path
  have sumLeConstant : le sumConstants constant := by
    have raised := add_le_add_right_iff
      (shift := sumConstants) |>.mpr one_nonnegative
    simpa only [zero_add, add_comm] using raised
  have scaled := mul_le_mul_nonnegative_right sumLeConstant
    deltaNonnegative
  exact le_trans path scaled

@[expose] public def ScalarContinuousAt {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension) : Prop :=
  ∀ tolerance : selection.Carrier, lt zero tolerance →
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ neighbor, FiniteVector.ball point radius neighbor →
        lt (abs (sub (function neighbor) (function point))) tolerance

public theorem totalValue_continuous_at_origin {dimension : Nat}
    (series : Convergent dimension) :
    ScalarContinuousAt (totalValue series)
      (FiniteVector.zeroVector dimension) := by
  let ratio := Problib.Analysis.Real.half one
  let outer := Problib.Analysis.Real.half series.radius
  let inner := mul ratio outer
  have ratioPositive := Problib.Analysis.Real.half_positive one_positive
  have outerPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have innerPositive : lt zero inner :=
    mul_positive ratioPositive outerPositive
  have ratioBelowOne : lt ratio one := by
    have raised := add_lt_add_left ratio ratioPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerBelow : lt outer series.radius := by
    have raised := add_lt_add_left outer outerPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => outer) := by
    intro coordinate
    change lt (abs (sub outer zero)) series.radius
    rw [sub_zero, abs_of_nonnegative outerPositive.left]
    exact outerBelow
  rcases value_lipschitz_box series ratioPositive.left
    ratioBelowOne outerPositive outerInside with
    ⟨constant, constantPositive, lipschitz⟩
  intro tolerance tolerancePositive
  have quotientPositive : lt zero (div tolerance constant) :=
    div_positive tolerancePositive constantPositive
  rcases small_positive innerPositive quotientPositive with
    ⟨delta, deltaPositive, belowInner, belowQuotient⟩
  refine ⟨delta, deltaPositive, fun neighbor near => ?_⟩
  have originBounds : ∀ coordinate,
      le (abs ((FiniteVector.zeroVector dimension) coordinate)) inner := by
    intro coordinate
    change le (abs zero) inner
    rw [abs_zero]
    exact innerPositive.left
  have neighborBounds : ∀ coordinate,
      le (abs (neighbor coordinate)) inner := by
    intro coordinate
    have close := near coordinate
    change lt (abs (sub (neighbor coordinate) zero)) delta at close
    rw [sub_zero] at close
    exact le_trans close.left belowInner
  have normNear : lt
      (FiniteVector.supNorm
        (FiniteVector.subVector neighbor
          (FiniteVector.zeroVector dimension))) delta :=
    (FiniteVector.ball_iff_sup_norm deltaPositive).mp near
  have bounded := lipschitz (FiniteVector.zeroVector dimension)
    neighbor originBounds neighborBounds
  have scaled := mul_lt_mul_positive_left normNear constantPositive
  have quotientBound := mul_le_mul_nonnegative_left belowQuotient
    constantPositive.left
  have cancel : mul constant (div tolerance constant) = tolerance :=
    mul_div_cancel tolerance (nonzero_of_positive constantPositive)
  rw [cancel] at quotientBound
  exact lt_of_le_of_lt bounded (lt_of_lt_of_le scaled quotientBound)

public theorem analytic_on_continuous_at {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (center : FiniteVector.carrier dimension) (member : region center) :
    ScalarContinuousAt function center := by
  rcases analytic.right center member with ⟨series, _, agree⟩
  have continuous := totalValue_continuous_at_origin series
  intro tolerance tolerancePositive
  rcases continuous tolerance tolerancePositive with
    ⟨seriesDelta, seriesDeltaPositive, close⟩
  rcases small_positive seriesDeltaPositive series.radiusPositive with
    ⟨delta, deltaPositive, belowDelta, belowRadius⟩
  refine ⟨delta, deltaPositive, fun neighbor near => ?_⟩
  let displacement := FiniteVector.subVector neighbor center
  have seriesNear : FiniteVector.ball
      (FiniteVector.zeroVector dimension) seriesDelta displacement := by
    intro coordinate
    have coordinateNear := near coordinate
    change lt (abs (sub (neighbor coordinate) (center coordinate)))
      delta at coordinateNear
    change lt (abs (sub (displacement coordinate) zero)) seriesDelta
    rw [sub_zero]
    exact lt_of_lt_of_le coordinateNear belowDelta
  have neighborInside : FiniteVector.ball center series.radius neighbor :=
    FiniteVector.ball_mono belowRadius near
  have centerInside : FiniteVector.ball center series.radius center :=
    FiniteVector.ball_center center series.radiusPositive
  have originInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (FiniteVector.zeroVector dimension) :=
    FiniteVector.ball_center _ series.radiusPositive
  have neighborEqual : function neighbor = totalValue series displacement := by
    have represented := agree neighbor neighborInside
    rw [totalValue_of_inside series displacement (by
      intro coordinate
      simpa [displacement, FiniteVector.ball, FiniteVector.zeroVector,
        FiniteVector.subVector, sub_zero] using
        neighborInside coordinate)]
    exact represented
  have centerEqual : function center =
      totalValue series (FiniteVector.zeroVector dimension) := by
    have represented := agree center centerInside
    have zeroDisplacement : FiniteVector.subVector center center =
        FiniteVector.zeroVector dimension := by
      funext coordinate
      simp [FiniteVector.subVector, FiniteVector.zeroVector, sub_self]
    have equal := value_congr series zeroDisplacement
      (by
        intro coordinate
        simpa only [FiniteVector.ball, FiniteVector.zeroVector,
          FiniteVector.subVector, sub_zero] using
          centerInside coordinate) originInside
    rw [totalValue_of_inside series _ originInside]
    exact represented.trans equal
  rw [neighborEqual, centerEqual]
  exact close displacement seriesNear

@[expose] public def AnalyticVectorOn {source target : Nat}
    (region : FiniteVector.carrier source → Prop)
    (function : FiniteVector.carrier source →
      FiniteVector.carrier target) : Prop :=
  ∀ coordinate : Fin target,
    AnalyticOn region (fun point => function point coordinate)

public theorem finite_small_radius {target : Nat}
    (radii : Fin target → selection.Carrier)
    (positive : ∀ coordinate, lt zero (radii coordinate))
    (indices : List (Fin target)) :
    ∃ radius : selection.Carrier,
      lt zero radius ∧
      ∀ coordinate, coordinate ∈ indices →
        le radius (radii coordinate) := by
  induction indices with
  | nil => exact ⟨one, one_positive, fun _ member =>
      False.elim (List.not_mem_nil member)⟩
  | cons selected rest induction =>
      rcases induction with ⟨restRadius, restPositive, restBound⟩
      rcases small_positive restPositive (positive selected) with
        ⟨radius, radiusPositive, belowRest, belowSelected⟩
      refine ⟨radius, radiusPositive, fun coordinate member => ?_⟩
      rcases List.mem_cons.mp member with equal | later
      · subst coordinate
        exact belowSelected
      · exact le_trans belowRest (restBound coordinate later)

public theorem analytic_vector_continuous_at {source target : Nat}
    {region : FiniteVector.carrier source → Prop}
    {function : FiniteVector.carrier source →
      FiniteVector.carrier target}
    (analytic : AnalyticVectorOn region function)
    (point : FiniteVector.carrier source) (member : region point) :
    FiniteVector.ContinuousAt function point := by
  intro tolerance tolerancePositive
  let coordinateContinuity := fun coordinate : Fin target =>
    analytic_on_continuous_at (analytic coordinate) point member
  let coordinateRadius := fun coordinate : Fin target =>
    Classical.choose
      (coordinateContinuity coordinate tolerance tolerancePositive)
  have radiusPositive : ∀ coordinate,
      lt zero (coordinateRadius coordinate) :=
    fun coordinate =>
      (Classical.choose_spec
        (coordinateContinuity coordinate tolerance tolerancePositive)).1
  rcases finite_small_radius coordinateRadius radiusPositive
    (List.finRange target) with ⟨radius, positive, below⟩
  refine ⟨radius, positive, fun neighbor near coordinate => ?_⟩
  have coordinateNear := FiniteVector.ball_mono
    (below coordinate (List.mem_finRange coordinate)) near
  exact (Classical.choose_spec
    (coordinateContinuity coordinate tolerance tolerancePositive)).2
    neighbor coordinateNear

end

end Problib.Analysis.Real.PowerSeries
