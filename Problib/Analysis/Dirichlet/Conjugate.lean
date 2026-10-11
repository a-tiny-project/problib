module

public import Problib.Analysis.Dirichlet.Density
public import Problib.Analysis.Categorical
public import Problib.Measure.Kernel.Density.Conditional
import Problib.Measure.Integral.Density.Algebra
import Problib.Measure.Product.Countable

/-! Dirichlet–categorical conjugacy.

`increment concentration observed` raises the observed concentration by one.
The power law `shapePower (a+1) v = shapePower a v · v` holds at every `v`, so
multiplying the Dirichlet weight by the coordinate `θₖ` raises the `k`-th shape
by one (`weight_mul_coordinate`).

`joint concentration observed θ` is the joint density of a Dirichlet draw `θ`
and one categorical observation `k` drawn from it. It is the prior density
times the likelihood `θₖ`. Its conditional kernel given the observation, read
against the simplex reference, is the Dirichlet law at the incremented
concentration (`posterior`). The mass of the joint density at `k` is the
predictive probability `αₖ/Σα` (`predictive`), the normalizer ratio
`B(α + eₖ)/B(α)` of `Dirichlet.family`. At every simplex point, `θₖ` is
the probability of `k` under the categorical law with weights `θ`
(`categorical_simplexPoint`). -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Dirichlet

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The concentration after one observation of `observed`: that concentration
is raised by one. -/
@[expose] public def increment {count : Nat} (concentration : Fin count → Carrier)
    (observed : Fin count) : Fin count → Carrier :=
  fun index => if index = observed then add (concentration index) one else concentration index

public theorem increment_self {count : Nat} (concentration : Fin count → Carrier)
    (observed : Fin count) :
    increment concentration observed observed = add (concentration observed) one := by
  unfold increment
  exact ite_eq_left rfl

public theorem increment_of_ne {count : Nat} (concentration : Fin count → Carrier)
    {index observed : Fin count} (different : index ≠ observed) :
    increment concentration observed index = concentration index := by
  unfold increment
  exact ite_eq_right different

/-- Raising one positive concentration keeps every concentration positive. -/
public theorem increment_positive {count : Nat} {concentration : Fin count → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (observed : Fin count)
    (index : Fin count) : lt zero (increment concentration observed index) := by
  by_cases same : index = observed
  · rw [same, increment_self]
    exact add_positive (positive observed) one_positive
  · rw [increment_of_ne _ same]
    exact positive index

private theorem finTail_increment_zero {count : Nat} (concentration : Fin (count + 1) → Carrier) :
    finTail count (increment concentration 0) = finTail count concentration :=
  funext fun index => increment_of_ne concentration (Fin.succ_ne_zero index)

private theorem finTail_increment_succ {count : Nat} (concentration : Fin (count + 1) → Carrier)
    (observed : Fin count) :
    finTail count (increment concentration observed.succ) =
      increment (finTail count concentration) observed := by
  funext index
  show increment concentration observed.succ index.succ =
    increment (finTail count concentration) observed index
  by_cases same : index = observed
  · rw [same]
    exact (increment_self concentration observed.succ).trans
      (increment_self (finTail count concentration) observed).symm
  · exact (increment_of_ne concentration (fun equal => same (Fin.succ_inj.mp equal))).trans
      (increment_of_ne (finTail count concentration) same).symm

/-- One observation adds one to the total concentration. -/
public theorem finSum_increment : (count : Nat) → (concentration : Fin count → Carrier) →
    (observed : Fin count) →
    additiveLaws.finSum count (increment concentration observed) =
      add (additiveLaws.finSum count concentration) one
  | 0, _, observed => Fin.elim0 observed
  | count + 1, concentration, observed => by
      rcases Fin.eq_zero_or_eq_succ observed with leading | ⟨rest, rfl⟩
      · subst leading
        show add (increment concentration 0 0)
            (additiveLaws.finSum count (finTail count (increment concentration 0))) =
          add (add (concentration 0) (additiveLaws.finSum count (finTail count concentration))) one
        rw [increment_self, finTail_increment_zero]
        ac_rfl
      · show add (increment concentration rest.succ 0)
            (additiveLaws.finSum count (finTail count (increment concentration rest.succ))) =
          add (add (concentration 0) (additiveLaws.finSum count (finTail count concentration))) one
        rw [increment_of_ne _ (Fin.succ_ne_zero rest).symm, finTail_increment_succ,
          finSum_increment count (finTail count concentration) rest, add_assoc]

/-- Multiplying the weight by a coordinate raises that coordinate's shape by
one, at every point. -/
public theorem weight_mul_coordinate : (count : Nat) → (concentration point : Fin count → Carrier) →
    (observed : Fin count) →
    ENNReal.mul (weight count concentration point) (ENNReal.ofReal (point observed)) =
      weight count (increment concentration observed) point
  | 0, _, _, observed => Fin.elim0 observed
  | count + 1, concentration, point, observed => by
      rcases Fin.eq_zero_or_eq_succ observed with leading | ⟨rest, rfl⟩
      · subst leading
        show ENNReal.mul (ENNReal.mul (shapePower (concentration 0) (point 0))
            (weight count (finTail count concentration) (finTail count point)))
            (ENNReal.ofReal (point 0)) =
          ENNReal.mul (shapePower (increment concentration 0 0) (point 0))
            (weight count (finTail count (increment concentration 0)) (finTail count point))
        rw [increment_self, finTail_increment_zero, shapePower_add_one]
        ac_rfl
      · show ENNReal.mul (ENNReal.mul (shapePower (concentration 0) (point 0))
            (weight count (finTail count concentration) (finTail count point)))
            (ENNReal.ofReal (point rest.succ)) =
          ENNReal.mul (shapePower (increment concentration rest.succ 0) (point 0))
            (weight count (finTail count (increment concentration rest.succ))
              (finTail count point))
        rw [increment_of_ne _ (Fin.succ_ne_zero rest).symm, finTail_increment_succ,
          ENNReal.mul_assoc]
        exact congrArg (ENNReal.mul (shapePower (concentration 0) (point 0)))
          (weight_mul_coordinate count (finTail count concentration) (finTail count point) rest)

/-- One observation scales the Gamma product by the observed concentration. -/
public theorem finProduct_gammaIntegral_increment : (count : Nat) →
    {concentration : Fin count → Carrier} → (∀ index, lt zero (concentration index)) →
    (observed : Fin count) →
    ENNReal.multiplicativeLaws.finProduct count
        (fun index => gammaIntegral (increment concentration observed index)) =
      ENNReal.mul (ENNReal.ofReal (concentration observed))
        (ENNReal.multiplicativeLaws.finProduct count fun index =>
          gammaIntegral (concentration index))
  | 0, _, _, observed => Fin.elim0 observed
  | count + 1, concentration, positive, observed => by
      rcases Fin.eq_zero_or_eq_succ observed with leading | ⟨rest, rfl⟩
      · subst leading
        show ENNReal.mul (gammaIntegral (increment concentration 0 0))
            (ENNReal.multiplicativeLaws.finProduct count fun index =>
              gammaIntegral (finTail count (increment concentration 0) index)) =
          ENNReal.mul (ENNReal.ofReal (concentration 0))
            (ENNReal.mul (gammaIntegral (concentration 0))
              (ENNReal.multiplicativeLaws.finProduct count fun index =>
                gammaIntegral (finTail count concentration index)))
        rw [increment_self, finTail_increment_zero, gammaIntegral_add_one (positive 0),
          ENNReal.mul_assoc]
      · show ENNReal.mul (gammaIntegral (increment concentration rest.succ 0))
            (ENNReal.multiplicativeLaws.finProduct count fun index =>
              gammaIntegral (finTail count (increment concentration rest.succ) index)) =
          ENNReal.mul (ENNReal.ofReal (concentration rest.succ))
            (ENNReal.mul (gammaIntegral (concentration 0))
              (ENNReal.multiplicativeLaws.finProduct count fun index =>
                gammaIntegral (finTail count concentration index)))
        rw [increment_of_ne _ (Fin.succ_ne_zero rest).symm, finTail_increment_succ,
          finProduct_gammaIntegral_increment count (concentration := finTail count concentration)
            (fun index => positive index.succ) rest]
        show ENNReal.mul (gammaIntegral (concentration 0))
            (ENNReal.mul (ENNReal.ofReal (concentration rest.succ))
              (ENNReal.multiplicativeLaws.finProduct count fun index =>
                gammaIntegral (finTail count concentration index))) = _
        ac_rfl

/-- At a simplex point `θ`, the categorical law with weights `θ` gives each
observation `k` probability `θₖ`. This is the likelihood in `joint`. -/
public theorem categorical_simplexPoint {dimension : Nat} {point : Fin dimension → Carrier}
    (member : simplexRegion dimension point) (observed : Fin (dimension + 1)) :
    categorical (List.finRange (dimension + 1))
        (fun index => NNReal.ofReal (simplexPoint dimension point index))
        (fun other => other = observed) =
      ENNReal.ofReal (simplexPoint dimension point observed) := by
  have total : NNReal.additiveLaws.listSum ((List.finRange (dimension + 1)).map fun index =>
      NNReal.ofReal (simplexPoint dimension point index)) = NNReal.one := by
    apply NNReal.ext
    rw [NNReal.additiveLaws.listSum_map_hom additiveLaws NNReal.toReal rfl (fun _ _ => rfl),
      NNReal.toReal_one, ← finSum_simplexPoint dimension point, additiveLaws.finSum_eq_listSum]
    exact additiveLaws.listSum_map_congr _ fun index _ =>
      NNReal.toReal_ofReal (simplexPoint_positive member index).1
  rw [categorical_apply_category (FiniteEnumeration.finRange _), categoricalShare, total,
    NNReal.div_one]
  rfl

/-- The joint density of a Dirichlet draw `θ` and one categorical observation
`k` drawn from it: the prior density times the likelihood `θₖ`. -/
@[expose] public def joint {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier)
    (observed : Fin (dimension + 1)) (point : Fin (dimension + 1) → Carrier) : ENNReal :=
  ENNReal.mul (density concentration point) (ENNReal.ofReal (point observed))

public theorem joint_measurable {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier) :
    ENNRealMeasurable
      (Space.product (Space.discrete (Fin (dimension + 1)))
        (Space.pi (fun _ : Fin (dimension + 1) => borel)))
      (fun pair => joint concentration pair.1 pair.2) :=
  ENNRealMeasurable.of_measurableMap
    (MeasurableMap.uncurry_of_countable_first Fin.val (fun _ _ equal => Fin.ext equal)
      (fun observed => ((density_measurable concentration).mul
        (ofReal_measurable.comp (Space.coordinate_measurable
          (fun _ : Fin (dimension + 1) => borel) observed))).measurableMap))

/-- The joint density at an observation is the prior's reciprocal mass times the
weight at the incremented concentration. -/
public theorem joint_eq {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier)
    (observed : Fin (dimension + 1)) (point : Fin (dimension + 1) → Carrier) :
    joint concentration observed point =
      ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
        (weight (dimension + 1) (increment concentration observed) point) := by
  unfold joint density
  rw [ENNReal.mul_assoc, weight_mul_coordinate]

private theorem inverseMass_nonzero {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))) ≠ ENNReal.zero := by
  intro vanishing
  have unit := mass_mul_inverse positive
  rw [vanishing, ENNReal.mul_zero] at unit
  exact ENNReal.one_ne_zero unit.symm

/-- Dirichlet–categorical conjugacy: given one observation `k`, the conditional
law of `θ` is the Dirichlet law with `αₖ` raised by one. -/
public theorem posterior {dimension : Nat} {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index))
    (fallback : Fin (dimension + 1) → Carrier) (observed : Fin (dimension + 1)) :
    Kernel.densityConditional (simplex dimension) (simplexSFinite dimension)
        (joint concentration) (joint_measurable concentration) fallback observed =
      law (increment concentration observed) := by
  have raised := increment_positive positive observed
  have fiber : Kernel.densityFiber (simplex dimension) (joint concentration) observed =
      Measure.smul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
        ((simplex dimension).withDensity
          (weight (dimension + 1) (increment concentration observed))) := by
    rw [Measure.smul_withDensity _ _ (weight_measurable _ _)]
    unfold Kernel.densityFiber
    apply congrArg
    funext point
    exact joint_eq concentration observed point
  have scaled := (weight_normalizable raised).smul
    (show ENNReal.Finite (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration)))) from
      True.intro)
    (inverseMass_nonzero positive)
  have defined : Measure.IsNormalizable
      (Kernel.densityFiber (simplex dimension) (joint concentration) observed) :=
    fiber ▸ scaled
  rw [Kernel.densityConditional_eq_normalize _ _ _ _ _ defined, law_eq_normalize raised]
  exact (Measure.normalize_congr fiber defined scaled).trans
    (Measure.normalize_smul _ _ _ _)

/-- The predictive probability of one observation `k` is `αₖ/Σα`: the mass of
the joint density at `k`. -/
public theorem predictive {dimension : Nat} {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (observed : Fin (dimension + 1)) :
    Kernel.densityMass (simplex dimension) (joint concentration) observed =
      ENNReal.ofReal
        (div (concentration observed) (additiveLaws.finSum (dimension + 1) concentration)) := by
  have totalPositive := finSum_positive dimension positive
  have ratio : ENNReal.mul (mass (increment concentration observed))
      (ENNReal.ofReal (additiveLaws.finSum (dimension + 1) concentration)) =
      ENNReal.mul (ENNReal.ofReal (concentration observed)) (mass concentration) := by
    apply ENNReal.mul_right_cancel_of_finite (gammaIntegral_finite totalPositive)
      (gammaIntegral_positive totalPositive)
    have incremented := mass_mul_gammaIntegral (increment concentration observed)
    rw [finSum_increment, gammaIntegral_add_one totalPositive,
      finProduct_gammaIntegral_increment (dimension + 1) positive observed,
      ← mass_mul_gammaIntegral concentration, ← ENNReal.mul_assoc,
      ← ENNReal.mul_assoc] at incremented
    exact incremented
  have coordinate : ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel))
      (fun point : Fin (dimension + 1) → Carrier => ENNReal.ofReal (point observed)) :=
    ofReal_measurable.comp
      (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) observed)
  have marginal := (family dimension).lintegral_law_of_scale (parameter := concentration)
    (updated := increment concentration observed) coordinate
    ((ENNReal.mul_comm _ _).trans (mass_mul_inverse positive))
    (fun point => (weight_mul_coordinate (dimension + 1) concentration point observed).trans
      (ENNReal.one_mul _).symm)
  rw [ENNReal.one_mul] at marginal
  have integral : Kernel.densityMass (simplex dimension) (joint concentration) observed =
      lintegral (law concentration) (fun point => ENNReal.ofReal (point observed)) := by
    rw [law_eq_withDensity positive,
      lintegral_withDensity _ (density_measurable concentration) coordinate]
    rfl
  rw [integral, show law concentration = (family dimension).law concentration from rfl,
    marginal]
  show ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
      (mass (increment concentration observed)) = _
  calc ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
        (mass (increment concentration observed))
      = ENNReal.mul (ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
          (mass (increment concentration observed)))
          (ENNReal.mul (ENNReal.ofReal (additiveLaws.finSum (dimension + 1) concentration))
            (ENNReal.ofReal (inverse (additiveLaws.finSum (dimension + 1) concentration)))) := by
        rw [ofReal_mul_ofReal_inverse totalPositive, ENNReal.mul_one]
    _ = ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
          (ENNReal.mul (ENNReal.mul (mass (increment concentration observed))
            (ENNReal.ofReal (additiveLaws.finSum (dimension + 1) concentration)))
            (ENNReal.ofReal (inverse (additiveLaws.finSum (dimension + 1) concentration)))) := by
        ac_rfl
    _ = ENNReal.mul (ENNReal.mul (mass concentration)
            (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration)))))
          (ENNReal.mul (ENNReal.ofReal (concentration observed))
            (ENNReal.ofReal (inverse (additiveLaws.finSum (dimension + 1) concentration)))) := by
        rw [ratio]
        ac_rfl
    _ = ENNReal.ofReal
          (div (concentration observed) (additiveLaws.finSum (dimension + 1) concentration)) := by
        rw [mass_mul_inverse positive, ENNReal.one_mul,
          ← ofReal_mul (positive observed).1 (inverse_nonnegative totalPositive.1),
          div_eq_mul_inverse]

end

end Problib.Analysis.Dirichlet
