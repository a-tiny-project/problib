module

public import Problib.Measure.Exchangeable.Latent
public import Problib.Measure.Kernel.Pi.Basic
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Product.Countable
import Problib.Measure.Kernel.Product.Algebra
import Problib.Measure.Kernel.Product.Transport

set_option autoImplicit false

/-!
# Keyed urns and local latent tables

`U.keyed encode injective` runs one copy of the urn `U` at each key of a type
`κ` that `encode` injects into the naturals. An observation is a key and a
value: it moves only its key's statistic, and its predictive is `U`'s at that
statistic.

A local latent presentation of `U` draws one value from a prior at each
statistic and scores each observation by a likelihood of that value. Its one
obligation (`LocalLatent.step`) is `U`'s predictive: scoring one observation
under the prior at `s` gives the predictive's mass times the prior at the
incorporated statistic. It is a latent presentation of `U` with one key
(`toLatent`). It also lifts to the keyed urn (`ofKeyed`). There the prior draws
every key's value independently from the local prior at that key's statistic
(`ofKeyed_prior`), and each observation reads the value at its own key.
Scoring an observation reweights only its key's value, so the local step at
that key is the keyed step.
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Pi

public section

universe u v

variable {α : Type u} {Y : Space α}

/-- A prior over one latent value at each statistic and a likelihood of that
value, whose one-step posterior is the urn's predictive. -/
structure Urn.LocalLatent (U : Urn.{u, v} Y) where
  Value : Type
  valueSpace : Space Value
  standard : StandardBorel valueSpace
  Valid : U.Stat → Prop
  valid_init : Valid U.init
  valid_inc : ∀ {s} y, Valid s → Valid (U.incorporate s y)
  prior : LawFamily U.statSpace valueSpace
  likelihood : α → Value → ENNReal
  likelihood_measurable : ∀ y, ENNRealMeasurable valueSpace (likelihood y)
  step : ∀ {s} y, Valid s →
    (prior.kernel s).withDensity (likelihood y) =
      Measure.smul (U.predictive s y) (prior.kernel (U.incorporate s y))

namespace Urn

variable (U : Urn.{u, v} Y) {κ : Type}

/-- Reading a keyed statistic at a key is jointly measurable. -/
theorem keyed_read_measurable (encode : κ → Nat) (injective : Function.Injective encode) :
    MeasurableMap (Space.product (Space.discrete κ) (Space.pi fun _ : κ => U.statSpace))
      U.statSpace fun pair => pair.2 pair.1 :=
  MeasurableMap.uncurry_of_countable_first encode injective
    (function := fun (key : κ) (s : κ → U.Stat) => s key)
    fun key => Space.coordinate_measurable (fun _ : κ => U.statSpace) key

/-- Incorporating an observation at its key is measurable. -/
theorem keyed_incorporate_measurable (encode : κ → Nat) (injective : Function.Injective encode) :
    MeasurableMap
      (Space.product (Space.pi fun _ : κ => U.statSpace) (Space.product (Space.discrete κ) Y))
      (Space.pi fun _ : κ => U.statSpace)
      fun pair => replace pair.1 pair.2.1 (U.incorporate (pair.1 pair.2.1) pair.2.2) := by
  have atKey : MeasurableMap
      (Space.product (Space.discrete κ) (Space.product (Space.pi fun _ : κ => U.statSpace) Y))
      (Space.pi fun _ : κ => U.statSpace)
      fun pair => replace pair.2.1 pair.1 (U.incorporate (pair.2.1 pair.1) pair.2.2) :=
    MeasurableMap.uncurry_of_countable_first encode injective
      (function := fun key (rest : (κ → U.Stat) × α) =>
        replace rest.1 key (U.incorporate (rest.1 key) rest.2))
      fun key => MeasurableMap.comp (replace_measurable key)
        (Space.pair_measurable (Space.first_measurable _ _)
          (MeasurableMap.comp U.incorporate_measurable
            (Space.pair_measurable
              (MeasurableMap.comp (Space.coordinate_measurable (fun _ : κ => U.statSpace) key)
                (Space.first_measurable _ _))
              (Space.second_measurable _ _))))
  intro set measurable
  exact MeasurableMap.comp atKey
    (Space.pair_measurable (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
      (Space.pair_measurable (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))) measurable

/-- The predictive at an observation's key is measurable. -/
theorem keyed_predictive_measurable (encode : κ → Nat) (injective : Function.Injective encode) :
    ENNRealMeasurable
      (Space.product (Space.pi fun _ : κ => U.statSpace) (Space.product (Space.discrete κ) Y))
      fun pair => U.predictive (pair.1 pair.2.1) pair.2.2 := by
  have atKey : MeasurableMap
      (Space.product (Space.discrete κ) (Space.product (Space.pi fun _ : κ => U.statSpace) Y))
      ennrealBorel fun pair => U.predictive (pair.2.1 pair.1) pair.2.2 :=
    MeasurableMap.uncurry_of_countable_first encode injective
      (function := fun key (rest : (κ → U.Stat) × α) => U.predictive (rest.1 key) rest.2)
      fun key => (ENNRealMeasurable.comp
        (map := fun pair : U.Stat × α => U.predictive pair.1 pair.2)
        (before := fun rest : (κ → U.Stat) × α => (rest.1 key, rest.2))
        U.predictive_measurable
        (Space.pair_measurable
          (MeasurableMap.comp (Space.coordinate_measurable (fun _ : κ => U.statSpace) key)
            (Space.first_measurable _ _))
          (Space.second_measurable _ _))).measurableMap
  exact ENNRealMeasurable.comp (ENNRealMeasurable.of_measurableMap atKey)
    (Space.pair_measurable (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
      (Space.pair_measurable (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _))))

/-- One copy of `U` at each key: an observation is a key and a value, and it
moves only its key's statistic. -/
@[expose] noncomputable def keyed (encode : κ → Nat) (injective : Function.Injective encode) :
    Urn.{u, v} (Space.product (Space.discrete κ) Y) where
  Stat := κ → U.Stat
  statSpace := Space.pi fun _ : κ => U.statSpace
  init := fun _ => U.init
  incorporate := fun s pair => replace s pair.1 (U.incorporate (s pair.1) pair.2)
  predictive := fun s pair => U.predictive (s pair.1) pair.2
  incorporate_measurable := keyed_incorporate_measurable U encode injective
  predictive_measurable := keyed_predictive_measurable U encode injective

namespace LocalLatent

variable {U} (L : U.LocalLatent)

/-- The likelihood of the one value an observation reads. -/
@[expose] noncomputable def single (likelihood : L.Value → ENNReal) : List L.Value → ENNReal
  | [value] => likelihood value
  | _ => ENNReal.one

/-- A value read as a table with one key. -/
theorem table_measurable :
    MeasurableMap L.valueSpace (Space.pi fun _ : Unit => L.valueSpace) fun value _ => value :=
  Space.pi_measurable fun _ => MeasurableMap.identity L.valueSpace

/-- A local latent presentation is a latent presentation with one key. -/
@[expose] noncomputable def toLatent : U.Latent where
  Key := Unit
  Value := L.Value
  valueSpace := L.valueSpace
  Valid := L.Valid
  valid_init := L.valid_init
  valid_inc := L.valid_inc
  prior := {
    kernel := L.prior.kernel.map _ L.table_measurable
    markov := fun s => (L.prior.markov s).map _ L.table_measurable }
  reads := fun _ => [()]
  likelihood := fun y => L.single (L.likelihood y)
  likelihood_measurable := fun y =>
    (L.likelihood_measurable y).comp (Space.coordinate_measurable (fun _ : Unit => L.valueSpace) ())
  step := fun {s} y valid =>
    calc ((L.prior.kernel s).map _ L.table_measurable).withDensity
          (fun table => L.likelihood y (table ()))
        = ((L.prior.kernel s).withDensity (L.likelihood y)).map _ L.table_measurable :=
          (Measure.map_withDensity _ _ L.table_measurable ((L.likelihood_measurable y).comp
            (Space.coordinate_measurable (fun _ : Unit => L.valueSpace) ()))).symm
      _ = (Measure.smul (U.predictive s y) (L.prior.kernel (U.incorporate s y))).map _
            L.table_measurable := by rw [L.step y valid]
      _ = _ := Measure.map_smul _ _ _ _

/-- Each key's local prior at that key's statistic, as one kernel. -/
@[expose] noncomputable def keyPrior (encode : κ → Nat) (injective : Function.Injective encode) :
    Kernel (Space.product (Space.discrete κ) (Space.pi fun _ : κ => U.statSpace)) L.valueSpace :=
  L.prior.kernel.precomp (fun pair => pair.2 pair.1) (keyed_read_measurable U encode injective)

/-- The keyed prior: every key draws its value independently from the local
prior at its own statistic. -/
@[expose] noncomputable def keyedPrior (encode : κ → Nat) (injective : Function.Injective encode) :
    LawFamily (U.keyed encode injective).statSpace (Space.pi fun _ : κ => L.valueSpace) where
  kernel := Kernel.pi encode
    (Kernel.Randomizer.ofStandardBorel (L.keyPrior encode injective) L.standard
      fun pair => L.prior.markov (pair.2 pair.1))
  markov := Kernel.pi_probability encode _

/-- At a keyed statistic, the keyed prior is the product of the local priors at
each key's statistic. -/
theorem ofKeyed_prior (encode : κ → Nat) (injective : Function.Injective encode) (s : κ → U.Stat) :
    IsProduct ((L.keyedPrior encode injective).kernel s) fun key => L.prior.kernel (s key) :=
  Kernel.pi_isProduct encode injective _ s

/-- Scoring one observation under the keyed prior reweights its key's value
alone: the local step there is the keyed step. -/
theorem keyed_step (encode : κ → Nat) (injective : Function.Injective encode) {s : κ → U.Stat}
    (key : κ) (y : α) (valid : L.Valid (s key)) :
    ((L.keyedPrior encode injective).kernel s).withDensity (fun table => L.likelihood y (table key)) =
      Measure.smul (U.predictive (s key) y)
        ((L.keyedPrior encode injective).kernel (replace s key (U.incorporate (s key) y))) := by
  let prior := (L.keyedPrior encode injective).kernel s
  have product := L.ofKeyed_prior encode injective s
  have finite : Measure.SFinite prior := Measure.SFinite.ofFinite product.probability.to_finite
  have redrawMeasurable : MeasurableMap (Space.product L.valueSpace (Space.pi fun _ : κ => L.valueSpace))
      (Space.pi fun _ : κ => L.valueSpace) fun pair => replace pair.2 key pair.1 :=
    MeasurableMap.comp (replace_measurable key) (Space.swap_measurable _ _)
  have redrawn : ∀ value, IsProduct
      ((Measure.prod (L.prior.kernel value) prior finite).map _ redrawMeasurable)
      fun other => L.prior.kernel (replace s key value other) := fun value =>
    (product.redraw key (L.prior.markov value) finite).congr_laws fun other =>
      (congrFun (apply_replace L.prior.kernel s key value) other).symm
  have drawn : (Measure.prod (L.prior.kernel (s key)) prior finite).map _ redrawMeasurable = prior :=
    ((redrawn (s key)).congr_laws fun other => by rw [replace_self]).ext product
  have densityMeasurable : ENNRealMeasurable (Space.pi fun _ : κ => L.valueSpace)
      fun table => L.likelihood y (table key) :=
    (L.likelihood_measurable y).comp (Space.coordinate_measurable (fun _ : κ => L.valueSpace) key)
  calc prior.withDensity (fun table => L.likelihood y (table key))
      = ((Measure.prod (L.prior.kernel (s key)) prior finite).map _ redrawMeasurable).withDensity
          (fun table => L.likelihood y (table key)) := by rw [drawn]
    _ = ((Measure.prod (L.prior.kernel (s key)) prior finite).withDensity
          fun pair => L.likelihood y (replace pair.2 key pair.1 key)).map _ redrawMeasurable :=
        (Measure.map_withDensity _ _ redrawMeasurable densityMeasurable).symm
    _ = (Measure.prod ((L.prior.kernel (s key)).withDensity (L.likelihood y)) prior finite).map _
          redrawMeasurable := by
        rw [Measure.prod_withDensity_left _ _ finite (L.likelihood_measurable y)]
        exact congrArg (fun density => (Measure.withDensity _ density).map _ redrawMeasurable)
          (funext fun pair => congrArg (L.likelihood y) (replace_same pair.2 key pair.1))
    _ = (Measure.prod (Measure.smul (U.predictive (s key) y)
          (L.prior.kernel (U.incorporate (s key) y))) prior finite).map _ redrawMeasurable := by
        rw [L.step y valid]
    _ = Measure.smul (U.predictive (s key) y)
          ((Measure.prod (L.prior.kernel (U.incorporate (s key) y)) prior finite).map _
            redrawMeasurable) := by
        rw [← Measure.map_smul]
        exact congrArg (fun measure => Measure.map measure _ redrawMeasurable)
          (Measure.semiproduct_smul _ _ _ _)
    _ = _ := congrArg (Measure.smul _)
        ((redrawn _).ext (L.ofKeyed_prior encode injective _))

/-- Incorporating an observation at its key keeps every key's statistic valid. -/
theorem valid_replace {s : κ → U.Stat} (key : κ) (y : α) (valid : ∀ other, L.Valid (s other))
    (other : κ) : L.Valid (replace s key (U.incorporate (s key) y) other) := by
  by_cases same : other = key
  · rw [same, replace_same]
    exact L.valid_inc y (valid key)
  · rw [replace_other _ _ same]
    exact valid other

/-- A local latent presentation lifts to the keyed urn: the prior draws every
key's value independently, and each observation reads the value at its key. -/
@[expose] noncomputable def ofKeyed (encode : κ → Nat) (injective : Function.Injective encode) :
    (U.keyed encode injective).Latent where
  Key := κ
  Value := L.Value
  valueSpace := L.valueSpace
  Valid := fun s => ∀ key, L.Valid (s key)
  valid_init := fun _ => L.valid_init
  valid_inc := fun pair valid => L.valid_replace pair.1 pair.2 valid
  prior := L.keyedPrior encode injective
  reads := fun pair => [pair.1]
  likelihood := fun pair => L.single (L.likelihood pair.2)
  likelihood_measurable := fun pair =>
    (L.likelihood_measurable pair.2).comp
      (Space.coordinate_measurable (fun _ : κ => L.valueSpace) pair.1)
  step := fun {_} pair valid => L.keyed_step encode injective pair.1 pair.2 (valid pair.1)

end LocalLatent

end Urn

end

end Problib.Measure.Exchangeable
