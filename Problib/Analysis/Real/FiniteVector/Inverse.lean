module

public import Problib.Analysis.Real.FiniteVector.Contraction
public import Problib.Analysis.Real.FiniteVector.Derivative

/-! The inverse function theorem.

A continuously differentiable map whose derivative at a point has an inverse
matches an open neighbourhood of the point one to one with an open
neighbourhood of its image, and the inverse is continuously differentiable,
with the inverse of the derivative as its derivative.

The proof is the contraction argument. Write `A` for the derivative at the
point and `B` for its inverse. Near the point the derivative stays within half
of `A` as measured through `B`, so `x ↦ x - B (f x)` halves distances there by
the mean value inequality. Solving `f x = y` is then finding a fixed point of
`x ↦ x - B (f x - y)`, which halves distances too. The same argument, applied
to linear maps, shows that every derivative near the point is invertible, with
a uniformly bounded inverse: solving `D w = v` is the fixed point of
`w ↦ B v + (w - B (D w))`. Only the sup norm is read, so the theorem holds in
every dimension. The dimension enters only through the hypothesis that the
derivative at the point has an inverse.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section


/-! ### Arithmetic of the radii -/

private theorem shrink_le {factor value : selection.Carrier} (factorNonnegative : le zero factor)
    (valueNonnegative : le zero value) :
    le (mul factor (div value (add factor one))) value := by
  have := one_positive
  have nonzero : add factor one ≠ zero := by real_grind
  have := div_nonnegative valueNonnegative (show le zero (add factor one) by real_grind)
  have identity : mul factor (div value (add factor one)) =
      sub value (div value (add factor one)) := by
    simp only [div]
    real_grind
  rw [identity]
  real_grind

private theorem shrink_lt {factor value : selection.Carrier} (factorNonnegative : le zero factor)
    (valuePositive : lt zero value) :
    lt (mul factor (div value (add factor one))) value := by
  have := one_positive
  have nonzero : add factor one ≠ zero := by real_grind
  have := mul_positive valuePositive
    (inverse_of_positive_positive (show lt zero (add factor one) by real_grind))
  have identity : mul factor (div value (add factor one)) =
      sub value (div value (add factor one)) := by
    simp only [div]
    real_grind
  rw [identity]
  simp only [div] at this ⊢
  real_grind

private theorem shrink_positive {factor value : selection.Carrier}
    (factorNonnegative : le zero factor) (valuePositive : lt zero value) :
    lt zero (div value (add factor one)) := by
  have := one_positive
  exact mul_positive valuePositive
    (inverse_of_positive_positive (show lt zero (add factor one) by real_grind))

/-- `factor` times something below `value / (factor + 1)` is below `value`. -/
private theorem scaled_lt {factor small value : selection.Carrier}
    (factorNonnegative : le zero factor) (smallNonnegative : le zero small)
    (below : lt small (div value (add factor one))) : lt (mul factor small) value := by
  have := one_positive
  have positive : lt zero (add factor one) := by real_grind
  have raised := mul_lt_mul_positive_right below positive
  rw [div_mul_cancel _ (nonzero_of_positive positive)] at raised
  have widened : le (mul factor small) (mul small (add factor one)) := by real_grind
  exact lt_of_le_of_lt widened raised

private theorem le_double_of_le_half_add {value error rest : selection.Carrier}
    (split : le value (add error rest)) (halved : le error (half value)) :
    le value (mul two rest) := by
  simp only [half, two] at halved ⊢
  real_grind

/-! ### Operators near an invertible one -/

section Near

variable {dimension : Nat} {base baseInverse near : BoundedLinear dimension dimension}

private theorem near_bound
    (close : ∀ value, le (supNorm (subVector value (baseInverse.map (near.map value))))
      (half (supNorm value)))
    (value : carrier dimension) :
    le (supNorm value) (mul (mul two baseInverse.bound) (supNorm (near.map value))) := by
  have split := supNorm_sub_triangle value (baseInverse.map (near.map value)) (zeroVector dimension)
  have atZero : ∀ vector : carrier dimension, subVector vector (zeroVector dimension) = vector := by
    intro vector
    funext coordinate
    exact sub_zero _
  rw [atZero, atZero] at split
  rw [mul_assoc]
  exact le_double_of_le_half_add
    (le_trans split (add_le_add (le_refl _) (baseInverse.bounded _))) (close value)

private theorem near_surjective (invertible : InverseOperators base baseInverse)
    (close : ∀ value, le (supNorm (subVector value (baseInverse.map (near.map value))))
      (half (supNorm value)))
    (target : carrier dimension) : ∃ value, near.map value = target := by
  rcases contraction_fixed (closed := fun _ => True) (fun _ _ _ _ => trivial)
      (map := fun value => addVector (baseInverse.map target)
        (subVector value (baseInverse.map (near.map value))))
      (fun _ _ => trivial) (fun first second _ _ => by
        have identity : subVector
            (addVector (baseInverse.map target) (subVector first (baseInverse.map (near.map first))))
            (addVector (baseInverse.map target)
              (subVector second (baseInverse.map (near.map second)))) =
            subVector (subVector first second)
              (baseInverse.map (near.map (subVector first second))) := by
          rw [near.map_sub, baseInverse.map_sub]
          funext coordinate
          simp only [addVector, subVector]
          real_grind
        rw [identity]
        exact close _)
      (start := zeroVector dimension) trivial with ⟨value, _, fixed, _, _⟩
  refine ⟨value, ?_⟩
  have equal : baseInverse.map (near.map value) = baseInverse.map target := by
    funext coordinate
    have atCoordinate := congrFun fixed coordinate
    simp only [addVector, subVector] at atCoordinate ⊢
    real_grind
  have applied := congrArg base.map equal
  rwa [invertible.right, invertible.right] at applied

/-- An operator within one half of an invertible operator, as measured through
its inverse, is invertible, and its inverse stretches by at most twice as much. -/
public theorem InverseOperators.of_near (invertible : InverseOperators base baseInverse)
    (close : ∀ value, le (supNorm (subVector value (baseInverse.map (near.map value))))
      (half (supNorm value))) :
    ∃ nearInverse : BoundedLinear dimension dimension,
      InverseOperators near nearInverse ∧ nearInverse.bound = mul two baseInverse.bound := by
  have injective : ∀ first second, near.map first = near.map second → first = second := by
    intro first second equal
    apply eq_of_supNorm_sub_nonpositive
    have bounded := near_bound close (subVector first second)
    rwa [near.map_sub, equal, supNorm_sub_self, mul_zero] at bounded
  have solves := fun target => Classical.choose_spec (near_surjective invertible close target)
  refine ⟨{
    map := fun target => Classical.choose (near_surjective invertible close target)
    additive := fun left right => injective _ _ (by rw [near.additive, solves, solves, solves])
    homogeneous := fun scalar value => injective _ _ (by rw [near.homogeneous, solves, solves])
    bound := mul two baseInverse.bound
    boundNonnegative :=
      mul_nonnegative (le_of_lt ofRat_two_positive) baseInverse.boundNonnegative
    bounded := fun target => by
      have bounded := near_bound close
        (Classical.choose (near_surjective invertible close target))
      rwa [solves] at bounded }, ⟨fun value => injective _ _ (solves _), solves⟩, rfl⟩

end Near

private theorem quarter_lt {value : selection.Carrier} (positive : lt zero value) :
    lt (half (half value)) value := by
  simp only [half, two]
  real_grind

private theorem add_half_eq (value : selection.Carrier) :
    add value (half value) = mul (add one (half one)) value := by
  simp only [half, two]
  real_grind

private theorem doubly_scaled_le {factor tolerance value : selection.Carrier}
    (factorNonnegative : le zero factor) (toleranceNonnegative : le zero tolerance)
    (valueNonnegative : le zero value) :
    le (mul factor (mul (div tolerance (add (mul factor factor) one)) (mul factor value)))
      (mul tolerance value) := by
  have square := mul_nonnegative factorNonnegative factorNonnegative
  have shrunk := mul_le_mul_nonnegative_right (shrink_le square toleranceNonnegative)
    valueNonnegative
  have regroup : mul factor (mul (div tolerance (add (mul factor factor) one)) (mul factor value)) =
      mul (mul (mul factor factor) (div tolerance (add (mul factor factor) one))) value := by
    real_grind
  rw [regroup]
  exact shrunk


private theorem double_lt_of_lt_half {value bound : selection.Carrier}
    (less : lt value (half bound)) : lt (mul two value) bound := by
  simp only [half, two] at less ⊢
  real_grind

private theorem half_le_half {value bound : selection.Carrier} (bounded : le value bound) :
    le (half value) (half bound) := by
  simp only [half, two]
  real_grind

/-! ### Rearrangements of vectors -/

section Rearrange

variable {dimension : Nat} (first second third fourth : carrier dimension)

private theorem rearrange_split :
    subVector first second = addVector
      (subVector (subVector first third) (subVector second fourth)) (subVector third fourth) := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_cancel :
    subVector (subVector first second) (subVector (subVector first third)
      (subVector second fourth)) = subVector third fourth := by
  funext coordinate
  simp only [subVector]
  real_grind

private theorem rearrange_shift (fifth : carrier dimension) :
    subVector (addVector (subVector first second) third) fourth =
      addVector (subVector (subVector first second) (subVector fourth fifth))
        (subVector third fifth) := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_start :
    subVector (addVector (subVector first second) third) first = subVector third second := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_translate :
    subVector (addVector first third) (addVector second third) = subVector first second := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_return : addVector first (subVector second first) = second := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_step : subVector (addVector first second) first = second := by
  funext coordinate
  simp only [addVector, subVector]
  real_grind

private theorem rearrange_fixed
    (fixed : addVector (subVector first second) third = first) : second = third := by
  funext coordinate
  have atCoordinate := congrFun fixed coordinate
  simp only [addVector, subVector] at atCoordinate
  real_grind

end Rearrange

/-! ### The residual map -/

/-- Where `function` has derivative `derivative`, the map `z ↦ z - B (function z)`
has derivative `I - B ∘ derivative`. -/
private theorem residual_derivative {dimension : Nat}
    {function : carrier dimension → carrier dimension} {point : carrier dimension}
    {derivative inverse : BoundedLinear dimension dimension}
    (differentiable : HasFrechetDerivative function point derivative) :
    HasFrechetDerivative (fun value => subVector value (inverse.map (function value))) point
      (BoundedLinear.difference (BoundedLinear.identity dimension)
        (BoundedLinear.compose inverse derivative)) := by
  intro epsilon positive
  rcases differentiable (div epsilon (add inverse.bound one))
    (shrink_positive inverse.boundNonnegative positive) with ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun displacement small => ?_⟩
  have identity : subVector
      (subVector (subVector (addVector point displacement)
          (inverse.map (function (addVector point displacement))))
        (subVector point (inverse.map (function point))))
      (subVector displacement (inverse.map (derivative.map displacement))) =
      subVector (zeroVector dimension) (inverse.map (subVector
        (subVector (function (addVector point displacement)) (function point))
        (derivative.map displacement))) := by
    rw [inverse.map_sub, inverse.map_sub]
    funext coordinate
    simp only [addVector, subVector, zeroVector]
    real_grind
  change le (supNorm (subVector
      (subVector (subVector (addVector point displacement)
          (inverse.map (function (addVector point displacement))))
        (subVector point (inverse.map (function point))))
      (subVector displacement (inverse.map (derivative.map displacement)))))
    (mul epsilon (supNorm displacement))
  rw [identity, supNorm_sub_comm, subVector_zero]
  refine le_trans (inverse.bounded _) ?_
  refine le_trans (mul_le_mul_nonnegative_left (close displacement small)
    inverse.boundNonnegative) ?_
  rw [← mul_assoc]
  exact mul_le_mul_nonnegative_right
    (shrink_le inverse.boundNonnegative (le_of_lt positive)) (supNorm_nonnegative _)

/-! ### The theorem -/

/-- Open neighbourhoods of `point` and of its image that `function` matches
one to one, with the inverse. -/
public structure LocalInverse {dimension : Nat}
    (region : carrier dimension → Prop)
    (function : carrier dimension → carrier dimension) (point : carrier dimension) where
  source : carrier dimension → Prop
  target : carrier dimension → Prop
  inverse : carrier dimension → carrier dimension
  sourceOpen : IsOpen source
  targetOpen : IsOpen target
  pointSource : source point
  sourceRegion : ∀ value, source value → region value
  mapsTo : ∀ value, source value → target (function value)
  inverseMapsTo : ∀ value, target value → source (inverse value)
  leftInverse : ∀ value, source value → inverse (function value) = value
  rightInverse : ∀ value, target value → function (inverse value) = value

/-- **The inverse function theorem.** A continuously differentiable map whose
derivative at `point` has an inverse is invertible near `point`, and its local
inverse is continuously differentiable, with derivative the inverse of the
map's derivative. -/
public theorem inverse_function {dimension : Nat}
    {region : carrier dimension → Prop}
    {function : carrier dimension → carrier dimension}
    {derivative : carrier dimension → BoundedLinear dimension dimension}
    (smooth : ContinuouslyDifferentiableOn region function derivative)
    {point : carrier dimension} (inside : region point)
    {pointInverse : BoundedLinear dimension dimension}
    (invertible : InverseOperators (derivative point) pointInverse) :
    ∃ chart : LocalInverse region function point,
      ∃ inverseDerivative : carrier dimension → BoundedLinear dimension dimension,
        (∀ value, chart.target value →
          InverseOperators (derivative (chart.inverse value)) (inverseDerivative value)) ∧
        ContinuouslyDifferentiableOn chart.target chart.inverse inverseDerivative := by
  have boundNonnegative := pointInverse.boundNonnegative
  have halfOne := half_positive one_positive
  -- A ball on which the derivative stays within one half of the derivative at
  -- `point`, measured through `pointInverse`.
  rcases smooth.continuous point inside _ (shrink_positive boundNonnegative halfOne) with
    ⟨near, nearPositive, nearClose⟩
  rcases smooth.isOpen point inside with ⟨within, withinPositive, withinRegion⟩
  rcases small_positive nearPositive withinPositive with
    ⟨radius, radiusPositive, radiusNear, radiusWithin⟩
  have inRegion : ∀ value, ball point radius value → region value := fun value inBall =>
    withinRegion value (ball_mono radiusWithin inBall)
  have halfClose : ∀ value, ball point radius value → ∀ vector,
      le (supNorm (subVector vector (pointInverse.map ((derivative value).map vector))))
        (half (supNorm vector)) := by
    intro value inBall vector
    have identity : subVector vector (pointInverse.map ((derivative value).map vector)) =
        pointInverse.map (subVector ((derivative point).map vector)
          ((derivative value).map vector)) := by
      rw [pointInverse.map_sub, invertible.left]
    rw [identity, half_eq_mul]
    refine le_trans (pointInverse.bounded _) ?_
    rw [supNorm_sub_comm]
    refine le_trans (mul_le_mul_nonnegative_left
      (nearClose value (ball_mono radiusNear inBall) vector) boundNonnegative) ?_
    rw [← mul_assoc]
    exact mul_le_mul_nonnegative_right (shrink_le boundNonnegative (le_of_lt halfOne))
      (supNorm_nonnegative _)
  -- Nearby derivatives are invertible, with inverses stretching at most twice as much.
  have inverses : ∀ value, ∃ inverse : BoundedLinear dimension dimension,
      ball point radius value →
        InverseOperators (derivative value) inverse ∧
          inverse.bound = mul two pointInverse.bound := by
    intro value
    by_cases inBall : ball point radius value
    · rcases InverseOperators.of_near invertible (halfClose value inBall) with
        ⟨inverse, inverts, bound⟩
      exact ⟨inverse, fun _ => ⟨inverts, bound⟩⟩
    · exact ⟨BoundedLinear.identity dimension, fun member => absurd member inBall⟩
  -- On the closed quarter ball, `z ↦ z - B (f z)` halves distances.
  have quarterPositive : lt zero (half (half radius)) :=
    half_positive (half_positive radiusPositive)
  have quarterBall : ∀ value, closedBall point (half (half radius)) value →
      ball point radius value := fun value member =>
    (ball_iff_supNorm radiusPositive).mpr (lt_of_le_of_lt member (quarter_lt radiusPositive))
  have openClosed : ∀ value, ball point (half (half radius)) value →
      closedBall point (half (half radius)) value := fun value member =>
    le_of_lt ((ball_iff_supNorm quarterPositive).mp member)
  have halves : ∀ first second, closedBall point (half (half radius)) first →
      closedBall point (half (half radius)) second →
        le (supNorm (subVector (subVector second (pointInverse.map (function second)))
          (subVector first (pointInverse.map (function first)))))
          (half (supNorm (subVector second first))) := by
    intro first second firstInside secondInside
    rw [half_eq_mul]
    exact supNorm_sub_le_of_derivative_bound
      (function := fun value => subVector value (pointInverse.map (function value)))
      (derivative := fun value => BoundedLinear.difference (BoundedLinear.identity dimension)
        (BoundedLinear.compose pointInverse (derivative value)))
      radiusPositive (le_of_lt halfOne)
      (fun value inBall => residual_derivative (smooth.differentiable value (inRegion value inBall)))
      (fun value inBall vector => by
        rw [← half_eq_mul]
        exact halfClose value inBall vector)
      firstInside secondInside
  generalize half (half radius) = quarter at quarterPositive quarterBall openClosed halves
  -- Images separate points of the quarter ball, and the map is Lipschitz there.
  have separated : ∀ first second, closedBall point quarter first →
      closedBall point quarter second →
        le (supNorm (subVector second first)) (mul (mul two pointInverse.bound)
          (supNorm (subVector (function second) (function first)))) := by
    intro first second firstInside secondInside
    have split := supNorm_triangle
      (subVector (subVector second (pointInverse.map (function second)))
        (subVector first (pointInverse.map (function first))))
      (subVector (pointInverse.map (function second)) (pointInverse.map (function first)))
    rw [← rearrange_split] at split
    rw [mul_assoc]
    exact le_double_of_le_half_add
      (le_trans split (add_le_add (le_refl _) (pointInverse.bounded_sub _ _)))
      (halves first second firstInside secondInside)
  have lipschitzNonnegative : le zero (mul (derivative point).bound (add one (half one))) :=
    mul_nonnegative (derivative point).boundNonnegative
      (le_of_lt (add_positive one_positive halfOne))
  have lipschitz : ∀ first second, closedBall point quarter first →
      closedBall point quarter second →
        le (supNorm (subVector (function second) (function first)))
          (mul (mul (derivative point).bound (add one (half one)))
            (supNorm (subVector second first))) := by
    intro first second firstInside secondInside
    have identity := congrArg (derivative point).map (rearrange_cancel second first
      (pointInverse.map (function second)) (pointInverse.map (function first)))
    rw [← pointInverse.map_sub, invertible.right] at identity
    rw [← identity]
    refine le_trans ((derivative point).bounded _) ?_
    rw [mul_assoc, ← add_half_eq]
    exact mul_le_mul_nonnegative_left (le_trans (supNorm_sub_le_add _ _)
      (add_le_add (le_refl _) (halves first second firstInside secondInside)))
      (derivative point).boundNonnegative
  -- Each value near `function point` has a preimage in the quarter ball.
  obtain ⟨reach, reachPositive, reachSmall⟩ : ∃ reach, lt zero reach ∧
      lt (mul pointInverse.bound reach) (half quarter) :=
    ⟨_, shrink_positive boundNonnegative (half_positive quarterPositive),
      shrink_lt boundNonnegative (half_positive quarterPositive)⟩
  have pointClosed : closedBall point quarter point := by
    show le (supNorm (subVector point point)) quarter
    rw [supNorm_sub_self]
    exact le_of_lt quarterPositive
  have solutions : ∀ target, ∃ value, ball (function point) reach target →
      ball point quarter value ∧ function value = target := by
    intro target
    by_cases near : ball (function point) reach target
    · have firstStep : le (supNorm (pointInverse.map (subVector target (function point))))
          (mul pointInverse.bound reach) :=
        le_trans (pointInverse.bounded _) (mul_le_mul_nonnegative_left
          (le_of_lt ((ball_iff_supNorm reachPositive).mp near)) boundNonnegative)
      rcases contraction_fixed (closed := closedBall point quarter)
          (fun _ _ inside converges => closedBall_limit inside converges)
          (map := fun value => addVector (subVector value (pointInverse.map (function value)))
            (pointInverse.map target))
          (fun value member => by
            show le (supNorm (subVector (addVector (subVector value
              (pointInverse.map (function value))) (pointInverse.map target)) point)) quarter
            rw [rearrange_shift _ _ _ _ (pointInverse.map (function point)),
              ← pointInverse.map_sub]
            refine le_trans (supNorm_triangle _ _) ?_
            rw [← add_half quarter]
            exact add_le_add (le_trans (halves point value pointClosed member) (half_le_half member))
              (le_trans firstStep (le_of_lt reachSmall)))
          (fun first second firstInside secondInside => by
            show le (supNorm (subVector
              (addVector (subVector first (pointInverse.map (function first)))
                (pointInverse.map target))
              (addVector (subVector second (pointInverse.map (function second)))
                (pointInverse.map target)))) _
            rw [rearrange_translate]
            exact halves second first secondInside firstInside)
          pointClosed with ⟨value, _, fixed, close, _⟩
      refine ⟨value, fun _ => ⟨(ball_iff_supNorm quarterPositive).mpr ?_, ?_⟩⟩
      · have start : le (supNorm (subVector value point)) (mul two (supNorm (subVector
            (addVector (subVector point (pointInverse.map (function point)))
              (pointInverse.map target)) point))) := close
        rw [rearrange_start, ← pointInverse.map_sub] at start
        exact lt_of_le_of_lt start (double_lt_of_lt_half (lt_of_le_of_lt firstStep reachSmall))
      · have applied := congrArg (derivative point).map (rearrange_fixed _ _ _ fixed)
        rwa [invertible.right, invertible.right] at applied
    · exact ⟨point, fun member => absurd member near⟩
  let inverse := fun target => Classical.choose (solutions target)
  have inverseSpec : ∀ target, ball (function point) reach target →
      ball point quarter (inverse target) ∧ function (inverse target) = target :=
    fun target => Classical.choose_spec (solutions target)
  have injective : ∀ first second, closedBall point quarter first →
      closedBall point quarter second → function first = function second → first = second := by
    intro first second firstInside secondInside equal
    have bound := separated second first secondInside firstInside
    rw [equal, supNorm_sub_self, mul_zero] at bound
    exact eq_of_supNorm_sub_nonpositive bound
  let chart : LocalInverse region function point := {
    source := fun value => ball point quarter value ∧ ball (function point) reach (function value)
    target := ball (function point) reach
    inverse := inverse
    sourceOpen := by
      intro value member
      rcases ball_is_open point quarterPositive value member.1 with
        ⟨first, firstPositive, firstBall⟩
      rcases ball_is_open (function point) reachPositive (function value) member.2 with
        ⟨second, secondPositive, secondBall⟩
      rcases small_positive firstPositive (shrink_positive lipschitzNonnegative secondPositive) with
        ⟨small, smallPositive, smallFirst, smallSecond⟩
      refine ⟨small, smallPositive, fun nearby near =>
        ⟨firstBall nearby (ball_mono smallFirst near), secondBall _ ?_⟩⟩
      apply (ball_iff_supNorm secondPositive).mpr
      exact lt_of_le_of_lt (lipschitz value nearby (openClosed value member.1)
          (openClosed nearby (firstBall nearby (ball_mono smallFirst near))))
        (scaled_lt lipschitzNonnegative (supNorm_nonnegative _)
          (lt_of_lt_of_le ((ball_iff_supNorm smallPositive).mp near) smallSecond))
    targetOpen := ball_is_open _ reachPositive
    pointSource := ⟨ball_center _ quarterPositive, ball_center _ reachPositive⟩
    sourceRegion := fun value member =>
      inRegion value (quarterBall value (openClosed value member.1))
    mapsTo := fun _ member => member.2
    inverseMapsTo := fun target member => ⟨(inverseSpec target member).1, by
      rw [(inverseSpec target member).2]
      exact member⟩
    leftInverse := fun value member => injective _ _
      (openClosed _ (inverseSpec _ member.2).1) (openClosed _ member.1) (inverseSpec _ member.2).2
    rightInverse := fun target member => (inverseSpec target member).2 }
  -- The inverse moves by at most twice `pointInverse`'s bound times the distance.
  have twoBound : le zero (mul two pointInverse.bound) :=
    mul_nonnegative (le_of_lt ofRat_two_positive) boundNonnegative
  have factorSquare := mul_nonnegative twoBound twoBound
  have inverseInside : ∀ target, ball (function point) reach target →
      closedBall point quarter (inverse target) := fun target member =>
    openClosed _ (inverseSpec target member).1
  have inverseNear : ∀ first second, ball (function point) reach first →
      ball (function point) reach second →
        le (supNorm (subVector (inverse second) (inverse first)))
          (mul (mul two pointInverse.bound) (supNorm (subVector second first))) := by
    intro first second firstMember secondMember
    have bound := separated _ _ (inverseInside first firstMember) (inverseInside second secondMember)
    rwa [(inverseSpec first firstMember).2, (inverseSpec second secondMember).2] at bound
  let inverseDerivative := fun target => Classical.choose (inverses (inverse target))
  have derivativeSpec : ∀ target, ball (function point) reach target →
      InverseOperators (derivative (inverse target)) (inverseDerivative target) ∧
        (inverseDerivative target).bound = mul two pointInverse.bound := fun target member =>
    Classical.choose_spec (inverses (inverse target)) (quarterBall _ (inverseInside target member))
  refine ⟨chart, inverseDerivative, fun target member => (derivativeSpec target member).1,
    ball_is_open _ reachPositive, ?_, ?_⟩
  · -- Differentiability: the inverse's increment is the inverse derivative of the
    -- map's increment, up to the map's own approximation error.
    intro target member epsilon positive
    rcases smooth.differentiable (inverse target)
        (inRegion _ (quarterBall _ (inverseInside target member))) _
        (shrink_positive factorSquare positive) with ⟨within', withinPositive', close⟩
    rcases ball_is_open (function point) reachPositive target member with
      ⟨room, roomPositive, roomBall⟩
    rcases small_positive roomPositive (shrink_positive twoBound withinPositive') with
      ⟨small, smallPositive, smallRoom, smallWithin⟩
    refine ⟨small, smallPositive, fun displacement short => ?_⟩
    have moved : ball (function point) reach (addVector target displacement) := roomBall _
      ((ball_iff_supNorm roomPositive).mpr (by
        rw [rearrange_step]
        exact lt_of_lt_of_le short smallRoom))
    have shift := inverseNear target (addVector target displacement) member moved
    rw [rearrange_step] at shift
    have residual := close (subVector (inverse (addVector target displacement)) (inverse target))
      (lt_of_le_of_lt shift (scaled_lt twoBound (supNorm_nonnegative _)
        (lt_of_lt_of_le short smallWithin)))
    rw [rearrange_return, (inverseSpec _ moved).2, (inverseSpec _ member).2,
      rearrange_step] at residual
    have inverts := derivativeSpec target member
    have identity : subVector (subVector (inverse (addVector target displacement)) (inverse target))
        ((inverseDerivative target).map displacement) =
        (inverseDerivative target).map (subVector ((derivative (inverse target)).map
          (subVector (inverse (addVector target displacement)) (inverse target))) displacement) := by
      rw [(inverseDerivative target).map_sub, inverts.1.left]
    change le (supNorm (subVector (subVector (inverse (addVector target displacement))
      (inverse target)) ((inverseDerivative target).map displacement)))
      (mul epsilon (supNorm displacement))
    rw [identity]
    refine le_trans ((inverseDerivative target).bounded _) ?_
    rw [inverts.2, supNorm_sub_comm]
    refine le_trans (mul_le_mul_nonnegative_left (le_trans residual
      (mul_le_mul_nonnegative_left shift (le_of_lt (shrink_positive factorSquare positive))))
      twoBound) ?_
    exact doubly_scaled_le twoBound (le_of_lt positive) (supNorm_nonnegative _)
  · -- Continuity of the inverse derivative, by the resolvent identity
    -- `M' - M = M' ∘ (D - D') ∘ M`.
    intro target member epsilon positive
    rcases smooth.continuous (inverse target)
        (inRegion _ (quarterBall _ (inverseInside target member))) _
        (shrink_positive factorSquare positive) with ⟨within', withinPositive', close⟩
    rcases ball_is_open (function point) reachPositive target member with
      ⟨room, roomPositive, roomBall⟩
    rcases small_positive roomPositive (shrink_positive twoBound withinPositive') with
      ⟨small, smallPositive, smallRoom, smallWithin⟩
    refine ⟨small, smallPositive, fun nearby near vector => ?_⟩
    have nearbyMember := roomBall nearby (ball_mono smallRoom near)
    have nearInverse : ball (inverse target) within' (inverse nearby) :=
      (ball_iff_supNorm withinPositive').mpr (lt_of_le_of_lt
        (inverseNear target nearby member nearbyMember)
        (scaled_lt twoBound (supNorm_nonnegative _)
          (lt_of_lt_of_le ((ball_iff_supNorm smallPositive).mp near) smallWithin)))
    have here := derivativeSpec target member
    have there := derivativeSpec nearby nearbyMember
    have identity : subVector ((inverseDerivative nearby).map vector)
        ((inverseDerivative target).map vector) =
        (inverseDerivative nearby).map (subVector
          ((derivative (inverse target)).map ((inverseDerivative target).map vector))
          ((derivative (inverse nearby)).map ((inverseDerivative target).map vector))) := by
      rw [(inverseDerivative nearby).map_sub, there.1.left, here.1.right]
    rw [identity]
    refine le_trans ((inverseDerivative nearby).bounded _) ?_
    rw [there.2, supNorm_sub_comm]
    have targetBound := (inverseDerivative target).bounded vector
    rw [here.2] at targetBound
    refine le_trans (mul_le_mul_nonnegative_left (le_trans (close _ nearInverse _)
      (mul_le_mul_nonnegative_left targetBound (le_of_lt (shrink_positive factorSquare positive))))
      twoBound) ?_
    exact doubly_scaled_le twoBound (le_of_lt positive) (supNorm_nonnegative _)

end

end Problib.Analysis.Real.FiniteVector
