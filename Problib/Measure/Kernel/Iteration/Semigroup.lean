module

set_option autoImplicit false

/-!
# Numerical semigroups

A set of step counts that contains zero, is closed under addition, and has
greatest common divisor one contains every large enough count. Finite
aperiodic chains and general-state small sets both read their eventual
minorization from it.
-/

namespace Problib.Measure.Kernel

private theorem semigroup_multiple (members : Nat → Prop)
    (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {value : Nat} (present : members value) (count : Nat) :
    members (count * value) := by
  induction count with
  | zero => simpa using zero
  | succ count induction =>
      rw [Nat.succ_mul]
      exact add (count * value) value induction present

private def ResidueReachable (members : Nat → Prop) (period residue : Nat) :
    Prop :=
  ∃ value, members value ∧ value % period = residue

private theorem residue_add (members : Nat → Prop) (period : Nat)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {first second : Nat}
    (left : ResidueReachable members period first)
    (right : ResidueReachable members period second) :
    ResidueReachable members period ((first + second) % period) := by
  rcases left with ⟨left, leftPresent, leftMod⟩
  rcases right with ⟨right, rightPresent, rightMod⟩
  refine ⟨left + right, add left right leftPresent rightPresent, ?_⟩
  rw [Nat.add_mod, leftMod, rightMod]

private theorem residue_inverse (members : Nat → Prop) (period : Nat)
    (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {residue : Nat} (present : ResidueReachable members period residue) :
    ∃ inverse, ResidueReachable members period inverse ∧
      (residue + inverse) % period = 0 := by
  rcases present with ⟨value, valuePresent, residueEqual⟩
  let inverse := ((period - 1) * value) % period
  refine ⟨inverse,
    ⟨(period - 1) * value,
      semigroup_multiple members zero add valuePresent (period - 1), rfl⟩,
    ?_⟩
  rw [← residueEqual]
  change (value % period + ((period - 1) * value) % period) % period = 0
  rw [← Nat.add_mod]
  have arithmetic : value + (period - 1) * value = period * value := by
    calc
      value + (period - 1) * value =
          (1 + (period - 1)) * value := by simp [Nat.add_mul]
      _ = period * value := by
        rw [Nat.add_comm, Nat.sub_add_cancel periodPositive]
  rw [arithmetic, Nat.mul_mod_right]

private theorem residue_sub (members : Nat → Prop) (period : Nat)
    (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {first second : Nat}
    (left : ResidueReachable members period first)
    (right : ResidueReachable members period second)
    (firstSmall : first < period) (included : second ≤ first) :
    ResidueReachable members period (first - second) := by
  rcases residue_inverse members period periodPositive zero add right with
    ⟨inverse, inversePresent, inverseZero⟩
  have sum := residue_add members period add left inversePresent
  have equal : (first + inverse) % period = first - second := by
    have decomposition : first + inverse =
        (first - second) + (second + inverse) := by omega
    rw [decomposition, Nat.add_mod, inverseZero, Nat.add_zero]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [equal] at sum
  exact sum

private theorem residue_min_positive (members : Nat → Prop) (period : Nat)
    (existsPositive : ∃ residue, 0 < residue ∧
      ResidueReachable members period residue) :
    ∃ least, 0 < least ∧ ResidueReachable members period least ∧
      ∀ residue, 0 < residue → residue < least →
        ¬ResidueReachable members period residue := by
  rcases existsPositive with ⟨candidate, positive, reachable⟩
  have descend : ∀ bound : Nat, 0 < bound →
      ResidueReachable members period bound →
      ∃ least, 0 < least ∧ ResidueReachable members period least ∧
        ∀ residue, 0 < residue → residue < least →
          ¬ResidueReachable members period residue := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound smaller =>
        intro boundPositive boundReachable
        by_cases existsSmaller : ∃ residue, 0 < residue ∧
            residue < bound ∧ ResidueReachable members period residue
        · rcases existsSmaller with
            ⟨residue, residuePositive, residueLess, ResidueReachable⟩
          exact smaller residue residueLess residuePositive ResidueReachable
        · refine ⟨bound, boundPositive, boundReachable, ?_⟩
          intro residue residuePositive residueLess ResidueReachable
          exact existsSmaller
            ⟨residue, residuePositive, residueLess, ResidueReachable⟩
  exact descend candidate positive reachable

private theorem residue_min_dvd (members : Nat → Prop) (period : Nat)
    (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    (least : Nat) (leastPositive : 0 < least)
    (leastReachable : ResidueReachable members period least)
    (minimal : ∀ residue, 0 < residue → residue < least →
      ¬ResidueReachable members period residue) :
    ∀ residue, ResidueReachable members period residue →
      least ∣ residue := by
  intro residue
  induction residue using Nat.strongRecOn with
  | ind residue smaller =>
      intro reachable
      by_cases isZero : residue = 0
      · subst residue
        exact ⟨0, by simp⟩
      have positive : 0 < residue := by omega
      have atLeast : least ≤ residue := by
        by_cases smallerThanLeast : residue < least
        · exact False.elim
            (minimal residue positive smallerThanLeast reachable)
        · omega
      have within : residue < period := by
        rcases reachable with ⟨value, _, equal⟩
        rw [← equal]
        exact Nat.mod_lt _ periodPositive
      have reduced := residue_sub members period periodPositive zero add
        reachable leastReachable within atLeast
      have reducedDvd : least ∣ residue - least :=
        smaller (residue - least) (by omega) reduced
      have decomposed : residue = (residue - least) + least := by omega
      rw [decomposed]
      exact Nat.dvd_add reducedDvd ⟨1, by simp⟩

private theorem residue_min_dvd_period (members : Nat → Prop)
    (period : Nat) (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    (least : Nat) (leastPositive : 0 < least)
    (leastReachable : ResidueReachable members period least)
    (minimal : ∀ residue, 0 < residue → residue < least →
      ¬ResidueReachable members period residue) : least ∣ period := by
  rcases residue_inverse members period periodPositive zero add
      leastReachable with ⟨inverse, inverseReachable, sumZero⟩
  have leastSmall : least < period := by
    rcases leastReachable with ⟨value, _, equal⟩
    rw [← equal]
    exact Nat.mod_lt _ periodPositive
  have inverseSmall : inverse < period := by
    rcases inverseReachable with ⟨value, _, equal⟩
    rw [← equal]
    exact Nat.mod_lt _ periodPositive
  have total : least + inverse = period := by
    by_cases small : least + inverse < period
    · rw [Nat.mod_eq_of_lt small] at sumZero
      omega
    · have enough : period ≤ least + inverse := by omega
      rw [Nat.mod_eq_sub_mod enough,
        Nat.mod_eq_of_lt (by omega)] at sumZero
      omega
  rw [← total]
  exact Nat.dvd_add ⟨1, by simp⟩
    (residue_min_dvd members period periodPositive zero add least
      leastPositive leastReachable minimal inverse inverseReachable)

private theorem residue_one_of_aperiodic (members : Nat → Prop)
    (period : Nat) (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    (aperiodic : ∀ divisor : Nat,
      (∀ steps, members steps → divisor ∣ steps) → divisor = 1) :
    ResidueReachable members period (1 % period) := by
  by_cases positive : ∃ residue, 0 < residue ∧
      ResidueReachable members period residue
  · rcases residue_min_positive members period positive with
      ⟨least, leastPositive, leastReachable, minimal⟩
    have periodDvd := residue_min_dvd_period members period
      periodPositive zero add least leastPositive leastReachable minimal
    have allDvd (steps : Nat) (present : members steps) :
        least ∣ steps :=
      (Nat.dvd_mod_iff periodDvd).mp
        (residue_min_dvd members period periodPositive zero add least
          leastPositive leastReachable minimal (steps % period)
          ⟨steps, present, rfl⟩)
    have one := aperiodic least allDvd
    rw [one] at leastReachable
    have oneSmall : 1 < period := by
      rcases leastReachable with ⟨value, _, equal⟩
      rw [← equal]
      exact Nat.mod_lt _ periodPositive
    rwa [Nat.mod_eq_of_lt oneSmall]
  · have allDvd (steps : Nat) (present : members steps) :
        period ∣ steps := by
      have zeroMod : steps % period = 0 := by
        by_cases equal : steps % period = 0
        · exact equal
        · have residuePositive : 0 < steps % period := by omega
          exact False.elim (positive
            ⟨steps % period, residuePositive, ⟨steps, present, rfl⟩⟩)
      exact Nat.dvd_of_mod_eq_zero zeroMod
    have one := aperiodic period allDvd
    subst period
    exact ⟨0, zero, by decide⟩

/-- A set of counts that contains zero and a positive member, is closed under
addition, and has no common divisor other than one contains every count past
some threshold. -/
public theorem numerical_semigroup_eventually (members : Nat → Prop)
    (period : Nat) (periodPositive : 0 < period)
    (periodPresent : members period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    (aperiodic : ∀ divisor : Nat,
      (∀ steps, members steps → divisor ∣ steps) → divisor = 1) :
    ∃ threshold, ∀ steps, threshold ≤ steps → members steps := by
  rcases residue_one_of_aperiodic members period periodPositive zero add
      aperiodic with ⟨unit, unitPresent, unitMod⟩
  refine ⟨period * unit, ?_⟩
  intro steps large
  let residue := steps % period
  have residueSmall : residue < period := Nat.mod_lt _ periodPositive
  have repeated : members (residue * unit) :=
    semigroup_multiple members zero add unitPresent residue
  have repeatedSmall : residue * unit ≤ steps := by
    exact Nat.le_trans (Nat.mul_le_mul_right unit (Nat.le_of_lt residueSmall))
      large
  have repeatedMod : (residue * unit) % period = residue := by
    rw [Nat.mul_mod, unitMod, ← Nat.mul_mod]
    simp [residue, Nat.mod_eq_of_lt residueSmall]
  have gapDvd : period ∣ steps - residue * unit := by
    have first : period ∣ steps - residue := by
      simpa only [residue] using
        (Nat.dvd_sub_mod (n := period) steps)
    have second : period ∣ residue * unit - residue := by
      simpa only [repeatedMod] using
        (Nat.dvd_sub_mod (n := period) (residue * unit))
    have combined := Nat.dvd_sub first second
    have residueLeRepeated : residue ≤ residue * unit := by
      simpa only [repeatedMod] using
        (Nat.mod_le (residue * unit) period)
    have residueLeSteps : residue ≤ steps := Nat.mod_le _ _
    have arithmetic : (steps - residue) -
        (residue * unit - residue) = steps - residue * unit := by
      omega
    rwa [arithmetic] at combined
  rcases gapDvd with ⟨count, gapEqual⟩
  have assembled : steps = residue * unit + period * count := by omega
  rw [assembled]
  exact add (residue * unit) (period * count) repeated
    (by simpa [Nat.mul_comm] using
      semigroup_multiple members zero add periodPresent count)

end Problib.Measure.Kernel
