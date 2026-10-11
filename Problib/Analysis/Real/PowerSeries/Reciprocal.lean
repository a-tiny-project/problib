module

public import Problib.Analysis.Real.PowerSeries.FiniteDerivative
public import Problib.Analysis.Real.PowerSeries.SubstitutionComposition

/-! The reciprocal is analytic away from zero.

Around a center `c ≠ 0`, `1 / (c + d) = (1 / c) Σ (-d / c)^n` whenever
`|d| < |c|`. Every center gets its own one-variable series, so no series is
ever recentered. Composition then carries the reciprocal through any analytic
function that does not vanish.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private theorem singleton_of_unique {α : Type} {list : List α} {element : α}
    (member : element ∈ list) (unique : ∀ other, other ∈ list → other = element)
    (nodup : list.Nodup) : list = [element] := by
  cases list with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail =>
      have headEqual := unique head List.mem_cons_self
      subst headEqual
      cases tail with
      | nil => rfl
      | cons next rest =>
          have nextEqual := unique next (List.mem_cons_of_mem _ List.mem_cons_self)
          subst nextEqual
          exact False.elim ((List.nodup_cons.mp nodup).left List.mem_cons_self)

/-- The one-variable multiindex of a degree. -/
@[expose] public def lineIndex (count : Nat) : MultiIndex.carrier 1 := fun _ => count

private theorem degreeShell_line (count : Nat) :
    MultiIndex.degreeShell 1 count = [lineIndex count] := by
  apply singleton_of_unique
  · exact MultiIndex.mem_degreeShell_iff.mpr rfl
  · intro index member
    have degreeEqual : index 0 + 0 = count := MultiIndex.degree_of_mem_shell member
    funext coordinate
    obtain ⟨value, bound⟩ := coordinate
    have single : value = 0 := by omega
    subst single
    exact degreeEqual
  · exact MultiIndex.degreeShell_nodup 1 count

/-- A one-variable shell is its single monomial. -/
public theorem shellTerm_line
    (coefficients : MultiIndex.carrier 1 → selection.Carrier)
    (displacement : FiniteVector.carrier 1) (count : Nat) :
    shellTerm coefficients displacement count =
      mul (coefficients (lineIndex count)) (power (displacement 0) count) := by
  unfold shellTerm
  rw [degreeShell_line, List.foldr_cons, List.foldr_nil, add_zero]
  change mul (coefficients (lineIndex count))
      (mul (power (displacement 0) count) one) = _
  rw [mul_one]

/-- A one-variable shell magnitude is its single monomial's magnitude. -/
public theorem shellMagnitude_line
    (coefficients : MultiIndex.carrier 1 → selection.Carrier)
    (displacement : FiniteVector.carrier 1) (count : Nat) :
    shellMagnitude coefficients displacement count =
      abs (mul (coefficients (lineIndex count))
        (power (displacement 0) count)) := by
  unfold shellMagnitude
  rw [degreeShell_line, List.foldr_cons, List.foldr_nil, add_zero]
  change abs (mul (coefficients (lineIndex count))
      (mul (power (displacement 0) count) one)) = _
  rw [mul_one]

/-- A signed geometric series with ratio below one in magnitude sums to the
reciprocal of its gap. -/
public theorem geometric_sum {ratio : selection.Carrier}
    (belowOne : lt (abs ratio) one) :
    sum (power ratio) (geometric_summable_of_abs_lt_one belowOne) =
      inverse (sub one ratio) := by
  let certificate := geometric_summable_of_abs_lt_one belowOne
  let total := sum (power ratio) certificate
  have gapPositive : lt zero (sub one ratio) :=
    sub_positive_iff.mpr (lt_of_le_of_lt (le_abs ratio) belowOne)
  have gapNonzero : sub one ratio ≠ zero := by
    intro vanished
    rw [vanished] at gapPositive
    exact lt_irrefl zero gapPositive
  have scaled := converges_to_scale (sub one ratio)
    (partialSum_converges (power ratio) certificate)
  have telescoped : (fun count => mul (sub one ratio)
      (partialSum (power ratio) count)) =
      (fun count => sub one (power ratio count)) := by
    funext count
    exact geometric_telescope ratio count
  rw [telescoped] at scaled
  have limit := converges_to_sub (converges_to_const one)
    (terms_converge_zero certificate)
  rw [sub_zero] at limit
  have product : mul (sub one ratio) total = one :=
    converges_to_unique scaled limit
  calc total = mul (mul (inverse (sub one ratio)) (sub one ratio)) total := by
        rw [inverse_mul_cancel gapNonzero, one_mul]
    _ = mul (inverse (sub one ratio)) (mul (sub one ratio) total) :=
        mul_assoc _ _ _
    _ = inverse (sub one ratio) := by rw [product, mul_one]

/-- The coefficients of `1 / (center + d)` in powers of `d`. -/
@[expose] public def reciprocalCoefficients (center : selection.Carrier) :
    MultiIndex.carrier 1 → selection.Carrier :=
  fun index => mul (inverse center) (power (neg (inverse center)) (index 0))

/-- The ratio of the geometric series behind `reciprocalCoefficients`. -/
@[expose] public def reciprocalRatio (center : selection.Carrier)
    (displacement : FiniteVector.carrier 1) : selection.Carrier :=
  mul (neg (inverse center)) (displacement 0)

private theorem reciprocal_tail (center : selection.Carrier)
    (displacement : FiniteVector.carrier 1) :
    tailTerms (reciprocalCoefficients center) displacement =
      fun count => mul (inverse center)
        (power (reciprocalRatio center displacement) (count + 1)) := by
  funext count
  unfold tailTerms
  rw [shellTerm_line]
  unfold reciprocalCoefficients reciprocalRatio lineIndex
  rw [mul_assoc, power_mul]

private theorem reciprocalRatio_small {center : selection.Carrier}
    (nonzero : center ≠ zero) {displacement : FiniteVector.carrier 1}
    (inside : lt (abs (displacement 0)) (abs center)) :
    lt (abs (reciprocalRatio center displacement)) one := by
  have absolutePositive := abs_positive_of_nonzero nonzero
  have scaled := mul_lt_mul_positive_left inside
    (inverse_of_positive_positive absolutePositive)
  have absoluteNonzero : abs center ≠ zero := by
    intro vanished
    rw [vanished] at absolutePositive
    exact lt_irrefl zero absolutePositive
  rw [inverse_mul_cancel absoluteNonzero] at scaled
  unfold reciprocalRatio
  rw [abs_mul, abs_neg, abs_inverse]
  exact scaled

private theorem power_succ_le {base : selection.Carrier}
    (nonnegative : le zero base) (atMostOne : le base one) (count : Nat) :
    le (power base (count + 1)) (power base count) := by
  rw [power_succ]
  have raised := mul_le_mul_nonnegative_right atMostOne
    (power_nonnegative nonnegative count)
  rwa [one_mul] at raised

public theorem reciprocal_normal {center : selection.Carrier}
    (nonzero : center ≠ zero) {displacement : FiniteVector.carrier 1}
    (inside : lt (abs (displacement 0)) (abs center)) :
    NormallyConvergent (reciprocalCoefficients center) displacement := by
  let ratio := abs (reciprocalRatio center displacement)
  have small : lt ratio one := reciprocalRatio_small nonzero inside
  have ratioNonnegative : le zero ratio := abs_nonnegative _
  refine ⟨mul (abs (inverse center)) (inverse (sub one ratio)),
    fun count => ?_⟩
  have magnitudes : tailMagnitudes (reciprocalCoefficients center)
      displacement = fun index => mul (abs (inverse center))
        (power ratio (index + 1)) := by
    funext index
    unfold tailMagnitudes
    rw [shellMagnitude_line]
    change abs (mul (mul (inverse center)
        (power (neg (inverse center)) (index + 1)))
        (power (displacement 0) (index + 1))) =
      mul (abs (inverse center))
        (power (abs (mul (neg (inverse center)) (displacement 0))) (index + 1))
    rw [mul_assoc, abs_mul, ← power_mul, abs_power]
  rw [magnitudes, partialSum_scale]
  apply mul_le_mul_nonnegative_left _ (abs_nonnegative _)
  exact le_trans
    (partialSum_le (power_succ_le ratioNonnegative (le_of_lt small)) count)
    (geometric_bounded ratioNonnegative small count)

public theorem displacement_inside {center : selection.Carrier}
    {displacement : FiniteVector.carrier 1}
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1) (abs center)
      displacement) :
    lt (abs (displacement 0)) (abs center) := by
  have first := inside 0
  simpa only [FiniteVector.zeroVector, sub_zero] using first

/-- The local series of the reciprocal at a nonzero center, on the ball whose
radius is the distance to zero. -/
@[expose] public def reciprocalSeries (center : selection.Carrier)
    (nonzero : center ≠ zero) : Convergent 1 where
  coefficients := reciprocalCoefficients center
  radius := abs center
  radiusPositive := abs_positive_of_nonzero nonzero
  normalOn := fun _ inside =>
    reciprocal_normal nonzero (displacement_inside inside)

public theorem reciprocalSeries_value {center : selection.Carrier}
    (nonzero : center ≠ zero) (displacement : FiniteVector.carrier 1)
    (inside : FiniteVector.ball (FiniteVector.zeroVector 1)
      (reciprocalSeries center nonzero).radius displacement) :
    value (reciprocalSeries center nonzero) displacement inside =
      inverse (add center (displacement 0)) := by
  let ratio := reciprocalRatio center displacement
  have small : lt (abs ratio) one :=
    reciprocalRatio_small nonzero (displacement_inside inside)
  let certificate := geometric_summable_of_abs_lt_one small
  have tail := partialSum_tail_converges (power ratio) certificate 1
  rw [geometric_sum small] at tail
  have firstPartial : partialSum (power ratio) 1 = one := by
    rw [partialSum_succ, partialSum_zero, zero_add, power_zero]
  rw [firstPartial] at tail
  have shifted : (fun index => power ratio (1 + index)) =
      (fun index => power ratio (index + 1)) := by
    funext index
    rw [Nat.add_comm]
  rw [shifted] at tail
  have scaled := converges_to_scale (inverse center) tail
  have partialEqual : (fun count => mul (inverse center)
      (partialSum (fun index => power ratio (index + 1)) count)) =
      partialSum (tailTerms (reciprocalCoefficients center) displacement) := by
    funext count
    rw [reciprocal_tail, partialSum_scale]
  rw [partialEqual] at scaled
  have tailSum := sum_eq_of_converges _
    (summable_of_absolute_bound
      ((reciprocalSeries center nonzero).absoluteOn displacement inside))
    scaled
  unfold value
  rw [tailSum]
  change add (reciprocalCoefficients center (MultiIndex.zeroIndex 1)) _ = _
  have constantTerm : reciprocalCoefficients center (MultiIndex.zeroIndex 1) =
      inverse center := by
    unfold reciprocalCoefficients
    rw [show MultiIndex.zeroIndex 1 0 = 0 from rfl, power_zero, mul_one]
  rw [constantTerm]
  have gap : sub one ratio = add one (mul (inverse center) (displacement 0)) := by
    change sub one (mul (neg (inverse center)) (displacement 0)) = _
    rw [sub_eq_add_neg, neg_mul, neg_neg]
  have product : add center (displacement 0) =
      mul center (add one (mul (inverse center) (displacement 0))) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_inverse_cancel nonzero, one_mul]
  rw [product, inverse_mul_total, ← gap]
  calc add (inverse center) (mul (inverse center)
        (sub (inverse (sub one ratio)) one)) =
      mul (inverse center) (add one (sub (inverse (sub one ratio)) one)) := by
        rw [mul_add, mul_one]
    _ = mul (inverse center) (inverse (sub one ratio)) := by
        rw [add_sub_cancel]

/-- A point closer to a center than the center is to zero is not zero. -/
public theorem nonzero_near {center neighbor : selection.Carrier}
    (close : lt (abs (sub neighbor center)) (abs center)) :
    neighbor ≠ zero := by
  intro vanished
  rw [vanished, abs_sub_comm, sub_zero] at close
  exact lt_irrefl _ close

/-- The vectors with a nonzero coordinate form an open set. -/
public theorem is_open_nonzero {dimension : Nat} (coordinate : Fin dimension) :
    FiniteVector.IsOpen
      (fun point : FiniteVector.carrier dimension => point coordinate ≠ zero) :=
  fun point nonzero => ⟨abs (point coordinate), abs_positive_of_nonzero nonzero,
    fun _ inside => nonzero_near (inside coordinate)⟩

/-- The reciprocal is analytic on the nonzero reals. -/
public theorem analytic_on_inverse :
    AnalyticOn (fun point : FiniteVector.carrier 1 => point 0 ≠ zero)
      (fun point => inverse (point 0)) := by
  refine ⟨is_open_nonzero 0, fun center member => ?_⟩
  · refine ⟨reciprocalSeries (center 0) member,
      fun point inside => nonzero_near (inside 0), ?_⟩
    intro point inside
    rw [reciprocalSeries_value]
    change inverse (point 0) =
      inverse (add (center 0) (sub (point 0) (center 0)))
    rw [add_sub_cancel]

/-- The reciprocal of an analytic function is analytic wherever the function
does not vanish. -/
public theorem analytic_on_inverse_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (nonzero : ∀ point, region point → function point ≠ zero) :
    AnalyticOn region (fun point => inverse (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_inverse nonzero

end

end Problib.Analysis.Real.PowerSeries
