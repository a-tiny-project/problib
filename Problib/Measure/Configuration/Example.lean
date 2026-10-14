module
public import Problib.Measure.Configuration.Reference
public import Problib.Measure.Configuration.Orbit

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real
public section

private def naturalNN (count : Nat) : NNReal :=
  NNReal.ofRat (count : Rat) (by exact_mod_cast Nat.zero_le count)

private theorem janossy_natural (count : Nat) :
    janossy count = NNReal.div NNReal.one (naturalNN (factorial count)) := by
  unfold janossy naturalNN
  rw [NNReal.ofReal_ofRat]
  rw [dite_eq_left (show (0 : Rat) ≤ (factorial count : Rat) from by
    exact_mod_cast Nat.zero_le (factorial count))]

private theorem naturalNN_mul (left right : Nat) :
    naturalNN (left * right) =
      NNReal.mul (naturalNN left) (naturalNN right) := by
  unfold naturalNN
  simpa only [Rat.natCast_mul] using
    (NNReal.ofRat_mul (left : Rat) (right : Rat)
      (by exact_mod_cast Nat.zero_le left)
      (by exact_mod_cast Nat.zero_le right))

private theorem factorial_positive (count : Nat) : 0 < factorial count := by
  induction count with
  | zero => decide
  | succ count induction =>
      exact Nat.mul_pos (Nat.succ_pos _) induction

private theorem naturalNN_positive {count : Nat} (positive : 0 < count) :
    NNReal.lt NNReal.zero (naturalNN count) := by
  unfold naturalNN
  rw [← NNReal.ofRat_zero]
  exact (NNReal.ofRat_lt_iff 0 (count : Rat)
    (by decide) (by exact_mod_cast Nat.zero_le count)).mpr
    (by exact_mod_cast positive)

private theorem naturalNN_nonzero {count : Nat} (positive : 0 < count) :
    naturalNN count ≠ NNReal.zero :=
  (NNReal.zero_lt_iff_ne_zero _).mp (naturalNN_positive positive)

private theorem reciprocal_ratio (base step : NNReal)
    (baseNonzero : base ≠ NNReal.zero)
    (stepNonzero : step ≠ NNReal.zero) :
    NNReal.div (NNReal.div NNReal.one base)
      (NNReal.div NNReal.one (NNReal.mul step base)) = step := by
  let product := NNReal.mul step base
  let reciprocal := NNReal.div NNReal.one product
  have productPositive : NNReal.lt NNReal.zero product :=
    NNReal.mul_positive
      ((NNReal.zero_lt_iff_ne_zero step).mpr stepNonzero)
      ((NNReal.zero_lt_iff_ne_zero base).mpr baseNonzero)
  have productNonzero : product ≠ NNReal.zero :=
    (NNReal.zero_lt_iff_ne_zero product).mp productPositive
  have reciprocalPositive : NNReal.lt NNReal.zero reciprocal :=
    NNReal.div_positive NNReal.one_positive productPositive
  have reciprocalNonzero : reciprocal ≠ NNReal.zero :=
    (NNReal.zero_lt_iff_ne_zero reciprocal).mp reciprocalPositive
  have multiplied : NNReal.mul step reciprocal =
      NNReal.div NNReal.one base := by
    apply NNReal.mul_right_cancel baseNonzero
    calc
      NNReal.mul (NNReal.mul step reciprocal) base =
          NNReal.mul product reciprocal := by
        dsimp [product]
        rw [NNReal.mul_assoc, NNReal.mul_comm reciprocal base,
          ← NNReal.mul_assoc]
      _ = NNReal.one := NNReal.mul_div_cancel NNReal.one productNonzero
      _ = NNReal.mul (NNReal.div NNReal.one base) base :=
        (NNReal.div_mul_cancel NNReal.one baseNonzero).symm
  apply NNReal.mul_right_cancel reciprocalNonzero
  calc
    NNReal.mul (NNReal.div (NNReal.div NNReal.one base) reciprocal)
        reciprocal = NNReal.div NNReal.one base :=
      NNReal.div_mul_cancel _ reciprocalNonzero
    _ = NNReal.mul step reciprocal := multiplied.symm

private theorem reciprocal_ratio_reverse (base step : NNReal)
    (baseNonzero : base ≠ NNReal.zero)
    (stepNonzero : step ≠ NNReal.zero) :
    NNReal.div (NNReal.div NNReal.one (NNReal.mul step base))
      (NNReal.div NNReal.one base) =
      NNReal.div NNReal.one step := by
  let first := NNReal.div NNReal.one base
  let second := NNReal.div NNReal.one (NNReal.mul step base)
  have firstNonzero : first ≠ NNReal.zero :=
    (NNReal.zero_lt_iff_ne_zero first).mp
      (NNReal.div_positive NNReal.one_positive
        ((NNReal.zero_lt_iff_ne_zero base).mpr baseNonzero))
  have productPositive : NNReal.lt NNReal.zero (NNReal.mul step base) :=
    NNReal.mul_positive
      ((NNReal.zero_lt_iff_ne_zero step).mpr stepNonzero)
      ((NNReal.zero_lt_iff_ne_zero base).mpr baseNonzero)
  have secondNonzero : second ≠ NNReal.zero :=
    (NNReal.zero_lt_iff_ne_zero second).mp
      (NNReal.div_positive NNReal.one_positive productPositive)
  have firstFactor : first = NNReal.mul step second := by
    have cancellation := NNReal.div_mul_cancel first secondNonzero
    rw [reciprocal_ratio base step baseNonzero stepNonzero] at cancellation
    exact cancellation.symm
  apply NNReal.mul_right_cancel firstNonzero
  calc
    NNReal.mul (NNReal.div second first) first = second :=
      NNReal.div_mul_cancel second firstNonzero
    _ = NNReal.mul (NNReal.div NNReal.one step) first := by
      calc
        second = NNReal.mul NNReal.one second :=
          (NNReal.one_mul second).symm
        _ = NNReal.mul (NNReal.mul (NNReal.div NNReal.one step) step)
            second := by rw [NNReal.div_mul_cancel NNReal.one stepNonzero]
        _ = NNReal.mul (NNReal.div NNReal.one step) first := by
          rw [NNReal.mul_assoc, ← firstFactor]

/-- Under Janossy coefficients, a birth from length `count` carries
the split-to-merge reference factor `count + 1`. -/
example (count : Nat) :
    coefficientRatio janossy 0 1 (count + 1) = naturalNN (count + 1) := by
  have factorialNext : naturalNN (factorial (count + 1)) =
      NNReal.mul (naturalNN (count + 1)) (naturalNN (factorial count)) := by
    change naturalNN ((count + 1) * factorial count) = _
    exact naturalNN_mul _ _
  have earlierNonzero : naturalNN (factorial count) ≠ NNReal.zero :=
    naturalNN_nonzero (factorial_positive count)
  have countNonzero : naturalNN (count + 1) ≠ NNReal.zero :=
    naturalNN_nonzero (Nat.succ_pos count)
  unfold coefficientRatio
  have predecessor : count + 1 + 0 - 1 = count := by omega
  rw [predecessor, janossy_natural count,
    janossy_natural (count + 1), factorialNext]
  exact reciprocal_ratio _ _ earlierNonzero countNonzero

/-- A death from length `count + 1` carries its reciprocal reference factor. -/
private theorem coefficientRatio_janossy_death_succ (count : Nat) :
    coefficientRatio janossy 1 0 count =
      NNReal.div NNReal.one (naturalNN (count + 1)) := by
  have factorialNext : naturalNN (factorial (count + 1)) =
      NNReal.mul (naturalNN (count + 1)) (naturalNN (factorial count)) := by
    change naturalNN ((count + 1) * factorial count) = _
    exact naturalNN_mul _ _
  have earlierNonzero : naturalNN (factorial count) ≠ NNReal.zero :=
    naturalNN_nonzero (factorial_positive count)
  have countNonzero : naturalNN (count + 1) ≠ NNReal.zero :=
    naturalNN_nonzero (Nat.succ_pos count)
  unfold coefficientRatio
  have successor : count + 1 - 0 = count + 1 := by omega
  rw [successor, janossy_natural count,
    janossy_natural (count + 1), factorialNext]
  exact reciprocal_ratio_reverse _ _ earlierNonzero countNonzero

/-- A death from positive length `length` has factor `1 / length`. -/
example (length : Nat) (positive : 0 < length) :
    coefficientRatio janossy 1 0 (length - 1) =
      NNReal.div NNReal.one (naturalNN length) := by
  cases length with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ count =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
        coefficientRatio_janossy_death_succ count

/-- Unit mass on each ordering of two Booleans. -/
@[expose] public noncomputable def boolPairCounting :
    Measure (Space.list (Space.discrete Bool)) :=
  Measure.listPower (unitCounting Bool.toNat) (unitCountingSFinite Bool.toNat) 2

private theorem bool_toNat_injective : Function.Injective Bool.toNat := by
  intro left right equal
  cases left <;> cases right <;> first | rfl | exact absurd equal (by decide)

/-- Each ordered Boolean pair has unit mass. -/
public theorem boolPairCounting_singleton (values : List Bool)
    (length : values.length = 2) :
    boolPairCounting (Set.singleton values) = ENNReal.one := by
  have unit := listPower_singleton_unit (unitCounting Bool.toNat)
    (unitCountingSFinite Bool.toNat) (fun _ => trivial)
    (unitCounting_singleton bool_toNat_injective) values
  rw [length] at unit
  exact unit

/-- A repeated pair has one ordering, since its stabilizer has order two. -/
public theorem orbitCount_bool_repeat (value : Bool) :
    orbitCount Bool.toNat [value, value] = ENNReal.one := by
  unfold orbitCount
  rw [Measure.map_apply _ _ (unorder_quotient_map (Space.discrete Bool)).measurable
      (unorder_singleton_measurable (element := Space.discrete Bool)
        (fun _ => trivial) _),
    unorder_preimage_singleton]
  have only : (fun other : List Bool => other.Perm [value, value]) =
      Set.singleton [value, value] :=
    funext fun _ => propext (List.perm_replicate (n := 2) (a := value))
  rw [only]
  exact listPower_singleton_unit _ _ (fun _ => trivial)
    (unitCounting_singleton bool_toNat_injective) [value, value]

/-- A distinct pair has two orderings, since its stabilizer is trivial. -/
public theorem orbitCount_bool_distinct :
    orbitCount Bool.toNat [false, true] = ennrealOfNat 2 := by
  have identity := orbitCount_mul_stabilizer bool_toNat_injective [false, true]
  change ENNReal.mul (ennrealOfNat 1) _ = ennrealOfNat 2 at identity
  rw [ennrealOfNat_one, ENNReal.one_mul] at identity
  exact identity

/-- No single factor turns ordered unit counting into unordered counting:
the orbits of `[false, false]` and `[false, true]` carry masses one and two
over atoms of mass one. -/
public theorem universal_factorial_fails :
    ¬ ∃ factor : ENNReal, ∀ values : List Bool, values.length = 2 →
      (boolPairCounting.map unorder
          (unorder_quotient_map (Space.discrete Bool)).measurable)
          (Set.singleton (unorder values)) =
        ENNReal.mul factor (boolPairCounting (Set.singleton values)) := by
  rintro ⟨factor, all⟩
  have repeated := all [false, false] rfl
  have distinct := all [false, true] rfl
  change orbitCount Bool.toNat [false, false] = _ at repeated
  change orbitCount Bool.toNat [false, true] = _ at distinct
  rw [orbitCount_bool_repeat, boolPairCounting_singleton _ rfl,
    ENNReal.mul_one] at repeated
  rw [orbitCount_bool_distinct, boolPairCounting_singleton _ rfl,
    ENNReal.mul_one, ← repeated, ← ennrealOfNat_one] at distinct
  unfold ennrealOfNat at distinct
  have below : (((2 : Nat) : Rat)) ≤ ((1 : Nat) : Rat) :=
    (ENNReal.ofRat_le_iff _ _ _ _).mp (by rw [distinct]; exact ENNReal.le_refl _)
  have natural : (2 : Nat) ≤ 1 := by exact_mod_cast below
  omega

end
end Problib.Measure
