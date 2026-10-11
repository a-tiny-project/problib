module

public import Problib.Measure.Exchangeable.Keyed
public import Problib.Measure.Exchangeable.Witness
public import Problib.Analysis.Dirichlet.Conjugate
public import Problib.Measure.StandardBorel.Pi
public import Problib.Measure.StandardBorel.Real
import Problib.Real.Grind

set_option autoImplicit false

/-!
# The Dirichlet–categorical urn

Observations are categories `Fin K` with `K = dimension + 1`. The statistic is
the count of each category. At counts `s`, the next category is `k` with
probability `(αₖ + sₖ)/Σ(α + s)` (`dirCatUrn`). The sites are the categories
themselves, so the raw history is the view and nothing is relabeled.

The category probabilities are a latent value: the prior at counts `s` is the
Dirichlet law at `α + s`, and a category is drawn with probability `θₖ`
(`dirCatLocal`). Its step is Dirichlet–categorical conjugacy from
`Analysis/Dirichlet/Conjugate.lean`: the scored prior is the joint density's
fiber at `k`, its mass the predictive (`Dirichlet.predictive`), and its
conditional the Dirichlet law at the incremented concentration
(`Dirichlet.posterior`). The latent value makes the raw history exchangeable
(`dirCat_exchangeable`), and the keyed urn lifts it to one vector of
probabilities per table (`dirCatTable`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind Problib.Analysis

public section

noncomputable section

variable {dimension : Nat}

/-- The concentration after the counts `s`. -/
@[expose] def posteriorConcentration (concentration : Fin (dimension + 1) → Carrier)
    (counts : Fin (dimension + 1) → Nat) : Fin (dimension + 1) → Carrier :=
  fun index => add (concentration index) (selection.ofRat (counts index : Rat))

theorem posteriorConcentration_positive {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (counts : Fin (dimension + 1) → Nat)
    (index : Fin (dimension + 1)) : lt zero (posteriorConcentration concentration counts index) := by
  have count := ofRat_nat_nonnegative (counts index)
  have base := positive index
  unfold posteriorConcentration
  real_grind

/-- One more observation of `observed` increments its concentration. -/
theorem posteriorConcentration_replace (concentration : Fin (dimension + 1) → Carrier)
    (counts : Fin (dimension + 1) → Nat) (observed : Fin (dimension + 1)) :
    posteriorConcentration concentration (Pi.replace counts observed (counts observed + 1)) =
      Dirichlet.increment (posteriorConcentration concentration counts) observed := by
  funext index
  by_cases same : index = observed
  · subst same
    rw [Dirichlet.increment_self]
    unfold posteriorConcentration
    rw [Pi.replace_same, Rat.natCast_add, Rat.natCast_ofNat, ofRat_add, ofRat_one]
    real_grind
  · rw [Dirichlet.increment_of_ne _ same]
    unfold posteriorConcentration
    rw [Pi.replace_other _ _ same]

/-- The probability `cₖ/Σc` of category `k` at concentration `c`. -/
@[expose] def share (concentration : Fin (dimension + 1) → Carrier)
    (observed : Fin (dimension + 1)) : ENNReal :=
  ENNReal.ofReal (div (concentration observed) (additiveLaws.finSum (dimension + 1) concentration))

theorem dirCat_incorporate_measurable :
    MeasurableMap (Space.product (Space.discrete (Fin (dimension + 1) → Nat))
        (Space.discrete (Fin (dimension + 1))))
      (Space.discrete (Fin (dimension + 1) → Nat))
      fun pair => Pi.replace pair.1 pair.2 (pair.1 pair.2 + 1) := by
  intro set measurable
  exact MeasurableMap.comp
    (MeasurableMap.uncurry_of_countable_first Fin.val (fun _ _ equal => Fin.ext equal)
      (function := fun (observed : Fin (dimension + 1)) (counts : Fin (dimension + 1) → Nat) =>
        Pi.replace counts observed (counts observed + 1))
      fun _ => MeasurableMap.from_discrete _ _)
    (Space.swap_measurable _ _) measurable

theorem dirCat_predictive_measurable (concentration : Fin (dimension + 1) → Carrier) :
    ENNRealMeasurable (Space.product (Space.discrete (Fin (dimension + 1) → Nat))
        (Space.discrete (Fin (dimension + 1))))
      fun pair => share (posteriorConcentration concentration pair.1) pair.2 := by
  have atCategory : MeasurableMap (Space.product (Space.discrete (Fin (dimension + 1)))
        (Space.discrete (Fin (dimension + 1) → Nat))) ennrealBorel
      fun pair => share (posteriorConcentration concentration pair.2) pair.1 :=
    MeasurableMap.uncurry_of_countable_first Fin.val (fun _ _ equal => Fin.ext equal)
      (function := fun (observed : Fin (dimension + 1)) (counts : Fin (dimension + 1) → Nat) =>
        share (posteriorConcentration concentration counts) observed)
      fun _ => MeasurableMap.from_discrete ennrealBorel _
  exact ENNRealMeasurable.comp
    (map := fun pair : Fin (dimension + 1) × (Fin (dimension + 1) → Nat) =>
      share (posteriorConcentration concentration pair.2) pair.1)
    (before := fun pair : (Fin (dimension + 1) → Nat) × Fin (dimension + 1) => (pair.2, pair.1))
    (ENNRealMeasurable.of_measurableMap atCategory) (Space.swap_measurable _ _)

/-- **The Dirichlet–categorical urn.** Its statistic is the count of each
category, and the next category is `k` with probability `(αₖ + sₖ)/Σ(α + s)`. -/
@[expose] def dirCatUrn (concentration : Fin (dimension + 1) → Carrier) :
    Urn.{0, 0} (Space.discrete (Fin (dimension + 1))) where
  Stat := Fin (dimension + 1) → Nat
  statSpace := Space.discrete _
  init := fun _ => 0
  incorporate := fun counts observed => Pi.replace counts observed (counts observed + 1)
  predictive := fun counts observed => share (posteriorConcentration concentration counts) observed
  incorporate_measurable := dirCat_incorporate_measurable
  predictive_measurable := dirCat_predictive_measurable concentration

/-- Each category once. -/
@[expose] def categoryCount (dimension : Nat) : Measure (Space.discrete (Fin (dimension + 1))) :=
  Measure.listSum ((List.finRange (dimension + 1)).map (Measure.dirac _))

theorem categoryCount_finite (dimension : Nat) : Measure.IsFinite (categoryCount dimension) := by
  unfold categoryCount
  induction (List.finRange (dimension + 1)) with
  | nil => exact Measure.IsFinite.zero _
  | cons head tail induction =>
      exact Measure.IsFinite.add (Measure.IsProbability.dirac _ head).to_finite induction

/-- A list sum of nonnegative weights is nonnegative. -/
private theorem listSum_nonnegative {weights : Fin (dimension + 1) → Carrier}
    (nonnegative : ∀ index, le zero (weights index)) :
    ∀ categories : List (Fin (dimension + 1)),
      le zero (additiveLaws.listSum (categories.map weights))
  | [] => by
      change le zero zero
      real_grind
  | index :: categories => by
      change le zero (add (weights index) (additiveLaws.listSum (categories.map weights)))
      have rest := listSum_nonnegative nonnegative categories
      have head := nonnegative index
      real_grind

/-- The shares of nonnegative weights over any list sum to their list sum's
share. -/
private theorem listSum_share {weights : Fin (dimension + 1) → Carrier} (total : Carrier)
    (nonnegative : ∀ index, le zero (weights index)) (totalPositive : lt zero total) :
    ∀ categories : List (Fin (dimension + 1)),
      ENNReal.additiveLaws.listSum (categories.map fun index =>
          ENNReal.ofReal (div (weights index) total)) =
        ENNReal.ofReal (div (additiveLaws.listSum (categories.map weights)) total)
  | [] => by
      change ENNReal.zero = ENNReal.ofReal (div zero total)
      rw [show div zero total = zero by real_grind, ENNReal.ofReal_zero]
  | index :: categories => by
      change ENNReal.add _ _ = ENNReal.ofReal (div (add _ _) total)
      have rest := listSum_nonnegative nonnegative categories
      rw [listSum_share total nonnegative totalPositive categories,
        ← ENNReal.ofReal_add (div_nonnegative (nonnegative index) totalPositive.1)
          (div_nonnegative rest totalPositive.1),
        show add (div (weights index) total) (div (additiveLaws.listSum (categories.map weights))
          total) = div (add (weights index) (additiveLaws.listSum (categories.map weights))) total
          by real_grind]

/-- At valid counts the categories' shares sum to one. -/
theorem share_total (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) (counts : Fin (dimension + 1) → Nat) :
    lintegral (categoryCount dimension) (share (posteriorConcentration concentration counts)) =
      ENNReal.one := by
  have weightsPositive := posteriorConcentration_positive positive counts
  have totalPositive := finSum_positive dimension weightsPositive
  unfold categoryCount
  rw [lintegral_listSum, List.map_map]
  have each : ∀ index : Fin (dimension + 1),
      lintegral (Measure.dirac (Space.discrete (Fin (dimension + 1))) index)
          (share (posteriorConcentration concentration counts)) =
        share (posteriorConcentration concentration counts) index :=
    fun index => lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)
  simp only [Function.comp_def, each, share]
  rw [listSum_share _ (fun index => (weightsPositive index).1) totalPositive,
    ← additiveLaws.finSum_eq_listSum, div_self (nonzero_of_positive totalPositive), ENNReal.ofReal_one]

/-- The urn's sampling kernel: each category with its share. -/
@[expose] def dirCatKernel (concentration : Fin (dimension + 1) → Carrier) :
    Kernel (Space.discrete (Fin (dimension + 1) → Nat)) (Space.discrete (Fin (dimension + 1))) where
  toFun := fun counts => (categoryCount dimension).withDensity
    (share (posteriorConcentration concentration counts))
  measurable := fun _ => ENNRealMeasurable.from_discrete _

/-- **Sampling.** At every count the urn draws each category with its share. -/
@[expose] def dirCatSampled (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) : (dirCatUrn concentration).Sampled where
  Valid := fun _ => True
  valid_measurable := Space.discrete_measurable _
  valid_init := trivial
  valid_inc := fun _ _ => trivial
  base := categoryCount dimension
  baseFinite := Measure.SFinite.ofFinite (categoryCount_finite dimension)
  kernel := dirCatKernel concentration
  kernelFinite := (Kernel.IsFinite.of_markov fun counts =>
    (show Measure.IsProbability ((categoryCount dimension).withDensity _) from ⟨by
      rw [Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
      exact share_total concentration positive counts⟩)).toSFinite
  markov := fun {counts} _ => ⟨by
    change (categoryCount dimension).withDensity _ Set.univ = _
    rw [Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
    exact share_total concentration positive counts⟩
  kernel_eq := fun _ => rfl

/-- **The Dirichlet–categorical step.** Scoring category `k` under the
Dirichlet law at `c` is `k`'s share times the Dirichlet law at `c` with `cₖ`
raised by one. -/
theorem dirichlet_step {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (observed : Fin (dimension + 1)) :
    (Dirichlet.law concentration).withDensity
        (fun point => ENNReal.ofReal (point observed)) =
      Measure.smul (share concentration observed)
        (Dirichlet.law (Dirichlet.increment concentration observed)) := by
  have coordinate : ENNRealMeasurable (Space.pi fun _ : Fin (dimension + 1) => borel)
      fun point : Fin (dimension + 1) → Carrier => ENNReal.ofReal (point observed) :=
    ofReal_measurable.comp
      (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) observed)
  have mass := Dirichlet.predictive positive observed
  rw [Dirichlet.law_eq_withDensity positive,
    Measure.withDensity_withDensity _ (Dirichlet.density_measurable concentration) coordinate]
  change Kernel.densityFiber (simplex dimension) (Dirichlet.joint concentration) observed = _
  rw [Kernel.densityFiber_eq_smul (simplex dimension) (simplexSFinite dimension)
      (Dirichlet.joint_measurable concentration) concentration observed
      (by rw [mass]; exact ENNReal.ofReal_finite _),
    mass, Dirichlet.posterior positive concentration observed]
  rfl

/-- **The local Dirichlet–categorical step.** Scoring category `k` under the
Dirichlet law after the counts `s` is `k`'s predictive times the Dirichlet law
after one more `k`. -/
theorem dirCatLocal_step (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) (counts : Fin (dimension + 1) → Nat)
    (observed : Fin (dimension + 1)) :
    (Dirichlet.law (posteriorConcentration concentration counts)).withDensity
        (fun point => ENNReal.ofReal (point observed)) =
      Measure.smul (share (posteriorConcentration concentration counts) observed)
        (Dirichlet.law (posteriorConcentration concentration
          (Pi.replace counts observed (counts observed + 1)))) := by
  rw [posteriorConcentration_replace]
  exact dirichlet_step (posteriorConcentration_positive positive counts) observed

/-- **The Dirichlet–categorical table.** The category probabilities are a
local latent value: Dirichlet at `α + s`, and a category `k` drawn with
probability `θₖ`. -/
@[expose] def dirCatLocal (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) : (dirCatUrn concentration).LocalLatent where
  Value := Fin (dimension + 1) → Carrier
  valueSpace := Space.pi fun _ => borel
  standard := StandardBorel.piOfNatInjection Fin.val (fun _ _ equal => Fin.ext equal)
    fun _ => StandardBorel.real
  Valid := fun _ => True
  valid_init := trivial
  valid_inc := fun _ _ => trivial
  prior := {
    kernel := (Dirichlet.kernel dimension).precomp (posteriorConcentration concentration)
      (MeasurableMap.from_discrete _ _)
    markov := fun counts => Dirichlet.law_isProbability (posteriorConcentration concentration counts) }
  likelihood := fun observed point => ENNReal.ofReal (point observed)
  likelihood_measurable := fun observed => ofReal_measurable.comp
    (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) observed)
  step := fun {counts} observed _ => dirCatLocal_step concentration positive counts observed

/-- The latent probabilities make the urn's raw history exchangeable. -/
theorem dirCat_exchangeable (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) :
    Exchangeable (dirCatUrn concentration) (dirCatSampled concentration positive)
      (View.raw (Space.discrete (Fin (dimension + 1)))) :=
  Witness.latent_raw (dirCatLocal concentration positive).toLatent _

/-- One vector of category probabilities per table key, drawn independently. -/
@[expose] def dirCatTable (concentration : Fin (dimension + 1) → Carrier)
    (positive : ∀ index, lt zero (concentration index)) {κ : Type} (encode : κ → Nat)
    (injective : Function.Injective encode) :
    ((dirCatUrn concentration).keyed encode injective).Latent :=
  (dirCatLocal concentration positive).ofKeyed encode injective

end

end

end Problib.Measure.Exchangeable
