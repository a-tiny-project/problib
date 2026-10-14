module

public import Problib.Analysis.Gaussian.Network.Basic
public import Problib.Analysis.Gaussian.SecondMoment
public import Problib.Measure.Configuration.Power
public import Problib.Measure.Kernel.Product.Density
public import Problib.Measure.Kernel.Precomp
public import Problib.Measure.Integral.Lebesgue.Extensionality
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Density.Algebra
import Problib.Real.Grind
import Problib.Measure.Measurability.Real

/-! The law of a linear-Gaussian network, its density and its moments.

The law is the left fold of scalar Gaussian kernels over the rows: node `i` is
drawn from `N(μᵢ + ⟨Bᵢ, x₍<ᵢ₎⟩, dᵢ)` given the prefix already drawn, and is
appended to it (`law_append`). The reference measure on lists of length `n` is
the `n`-fold product of Lebesgue measure (`listVolume`), and the density
against it is the product of the scalar conditionals, zero off length `n`
(`law_eq_withDensity`). No `n`-dimensional Jacobian appears: each step extends
a product by one coordinate.

The first and second moments are the recurrences of `Network.Basic`
(`moments_eq`). Dropping the last node marginalizes it (`marginal_last`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Reading lists of reals -/

/-- Coordinate `i`, zero beyond the end. -/
@[expose] public def entry (values : List Carrier) (index : Nat) : Carrier :=
  values.getD index zero

public theorem entry_measurable (index : Nat) :
    MeasurableMap (Space.list borel) borel (fun values => entry values index) := by
  have equal : (fun values : List Carrier => entry values index) = fun values =>
      Sum.elim (fun _ => zero) (fun value => value) (ListSpace.coordinate index values) := by
    funext values
    induction values generalizing index with
    | nil => simp [entry, ListSpace.coordinate]
    | cons head tail induction =>
        cases index with
        | zero => rfl
        | succ index => exact induction index
  rw [equal]
  measurability [ListSpace.coordinate_measurable borel index]

@[simp] public theorem dot_nil_left (values : List Carrier) : dot [] values = zero := by
  cases values <;> rfl

@[simp] public theorem dot_nil_right
    (coefficients : List Carrier) : dot coefficients [] = zero := by
  cases coefficients <;> rfl

/-- Peel the first coefficient off, reading the first coordinate as zero when absent. -/
public theorem dot_cons_left (coefficient : Carrier) (coefficients values : List Carrier) :
    dot (coefficient :: coefficients) values =
      add (mul coefficient (entry values 0)) (dot coefficients values.tail) := by
  cases values with
  | nil =>
      change zero = add (mul coefficient zero) (dot coefficients [])
      rw [dot_nil_right, mul_zero, add_zero]
  | cons value values => rfl

public theorem dot_measurable (coefficients : List Carrier) :
    MeasurableMap (Space.list borel) borel (fun values => dot coefficients values) := by
  induction coefficients with
  | nil =>
      simp only [dot_nil_left]
      exact MeasurableMap.constant _ borel zero
  | cons coefficient coefficients induction =>
      simp only [dot_cons_left]
      exact measurable_add
        (measurable_mul (MeasurableMap.constant _ borel coefficient) (entry_measurable 0))
        (MeasurableMap.comp induction (ListSpace.tail_measurable borel))

/-- Extending the values past the coefficients leaves the sum unchanged. -/
public theorem dot_append_right {coefficients values : List Carrier} (extra : List Carrier)
    (short : coefficients.length ≤ values.length) :
    dot coefficients (values ++ extra) = dot coefficients values := by
  induction coefficients generalizing values with
  | nil => simp
  | cons coefficient coefficients induction =>
      cases values with
      | nil => simp at short
      | cons value values =>
          change add (mul coefficient value) (dot coefficients (values ++ extra)) =
            add (mul coefficient value) (dot coefficients values)
          rw [induction (by simpa using short)]

public theorem entry_append_left {values : List Carrier} (extra : List Carrier) {index : Nat}
    (below : index < values.length) : entry (values ++ extra) index = entry values index := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left below]

@[simp] public theorem entry_concat_length (values : List Carrier) (value : Carrier) :
    entry (values ++ [value]) values.length = value := by
  simp [entry]

/-- Append one coordinate at the end. -/
@[expose] public def snoc (pair : List Carrier × Carrier) : List Carrier := pair.1 ++ [pair.2]

public theorem snoc_measurable :
    MeasurableMap (Space.product (Space.list borel) borel) (Space.list borel) snoc := by
  have equal : snoc = fun pair => (pair.2 :: pair.1.reverse).reverse := by
    funext pair
    simp [snoc]
  rw [equal]
  measurability [reverse_measurable borel, ListSpace.cons_measurable borel]

public theorem dropLast_measurable :
    MeasurableMap (Space.list borel) (Space.list borel) (List.dropLast (α := Carrier)) := by
  have equal : List.dropLast (α := Carrier) = fun values => values.reverse.tail.reverse := by
    funext values
    rw [List.tail_reverse, List.reverse_reverse]
  rw [equal]
  measurability [reverse_measurable borel, ListSpace.tail_measurable borel]

/-! ### The reference measure on lists -/

/-- The `n`-fold product of Lebesgue measure, on lists of length `n`. -/
@[expose] public def listVolume (count : Nat) : Measure (Space.list borel) :=
  Measure.listPower volume volumeSFinite count

public def listVolumeSFinite (count : Nat) : Measure.SFinite (listVolume count) :=
  Measure.SFinite.listPower volumeSFinite count

/-- The list volume is carried by lists of its own length. -/
public theorem listVolume_length_null (count : Nat) :
    listVolume count (fun values => values.length ≠ count) = ENNReal.zero :=
  Measure.listPower_length_null volume volumeSFinite count

/-- One more coordinate, appended at the end. -/
public theorem listVolume_succ (count : Nat) :
    listVolume (count + 1) =
      (Measure.prod (listVolume count) volume volumeSFinite).map snoc snoc_measurable := by
  unfold listVolume
  rw [← Measure.insertIdx_power volume volumeSFinite (Nat.le_refl count)]
  apply Measure.map_congr_on _ (region := fun pair : List Carrier × Carrier =>
    pair.1.length = count)
  · have complement : Set.complement (fun pair : List Carrier × Carrier =>
        pair.1.length = count) =
        Set.product (fun values : List Carrier => values.length ≠ count) Set.univ := by
      funext pair
      exact propext ⟨fun different => ⟨different, True.intro⟩, fun inside => inside.1⟩
    have lengthMeasurable : (Space.list borel).Measurable
        (fun values : List Carrier => values.length ≠ count) :=
      ListSpace.length_measurable borel (set := fun length => length ≠ count) trivial
    rw [complement, Measure.prod_apply_product _ _ _ lengthMeasurable borel.univ,
      Measure.listPower_length_null, ENNReal.zero_mul]
  · intro pair counted
    change pair.1.insertIdx count pair.2 = pair.1 ++ [pair.2]
    rw [← counted]
    exact List.insertIdx_length_self

/-! ### The scalar conditionals -/

/-- The conditional mean of a row given the earlier nodes. -/
@[expose] public def Row.mean (row : Row) (values : List Carrier) : Carrier :=
  add row.intercept (dot row.coefficients values)

public theorem Row.mean_measurable (row : Row) :
    MeasurableMap (Space.list borel) borel row.mean :=
  measurable_add (MeasurableMap.constant _ borel row.intercept) (dot_measurable row.coefficients)

/-- The scalar Gaussian kernel of a row, from the earlier nodes. -/
@[expose] public def Row.kernel (row : Row) : Kernel (Space.list borel) borel :=
  Gaussian.kernel.precomp (fun values => (row.mean values, row.variance))
    (Space.pair_measurable row.mean_measurable (MeasurableMap.constant _ borel row.variance))

public theorem Row.kernel_apply (row : Row) (values : List Carrier) :
    row.kernel values = Gaussian.law (row.mean values) row.variance :=
  rfl

public theorem Row.kernel_isProbability (row : Row) (values : List Carrier) :
    Measure.IsProbability (row.kernel values) :=
  Gaussian.law_isProbability _ _

public def Row.kernelSFinite (row : Row) : Kernel.IsSFinite row.kernel :=
  (Kernel.IsFinite.of_markov row.kernel_isProbability).toSFinite

/-- The joint density of the next node given the earlier ones. -/
@[expose] public def Row.pairDensity (row : Row) (pair : List Carrier × Carrier) : ENNReal :=
  ENNReal.finite (Gaussian.density (row.mean pair.1) row.variance pair.2)

public theorem Row.pairDensity_measurable (row : Row) :
    ENNRealMeasurable (Space.product (Space.list borel) borel) row.pairDensity := by
  have parameters : MeasurableMap (Space.product (Space.list borel) borel)
      (Space.product (Space.product borel borel) borel)
      (fun pair : List Carrier × Carrier => ((row.mean pair.1, row.variance), pair.2)) := by
    have mean : MeasurableMap (Space.product (Space.list borel) borel) (Space.product borel borel)
        (fun pair : List Carrier × Carrier => (row.mean pair.1, row.variance)) := by
      measurability [row.mean_measurable]
    measurability [mean]
  have composed := ENNRealMeasurable.comp Gaussian.density_measurable parameters
  exact composed

/-- The scalar conditional density of node `i` within a full list. -/
@[expose] public def Row.density (row : Row) (values : List Carrier) (index : Nat) : NNReal :=
  Gaussian.density (row.mean values) row.variance (entry values index)

public theorem Row.density_measurable (row : Row) (index : Nat) :
    ENNRealMeasurable (Space.list borel) (fun values => ENNReal.finite
      (row.density values index)) := by
  have parameters : MeasurableMap (Space.list borel)
      (Space.product (Space.product borel borel) borel)
      (fun values => ((row.mean values, row.variance), entry values index)) := by
    measurability [row.mean_measurable, entry_measurable index]
  have composed := ENNRealMeasurable.comp Gaussian.density_measurable parameters
  exact composed

/-! ### The law -/

/-- One step of the fold: draw the next node and append it. -/
@[expose] public def appendLaw (law : Measure (Space.list borel)) (row : Row) :
    Measure (Space.list borel) :=
  (law.semiproduct row.kernel row.kernelSFinite).map snoc snoc_measurable

/-- The network's law: the left fold of its rows' Gaussian kernels from the empty list. -/
@[expose] public def Network.law (network : Network) : Measure (Space.list borel) :=
  network.rows.foldl appendLaw (Measure.dirac _ [])

public theorem Network.law_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).law = appendLaw network.law row := by
  simp [Network.law, Network.append, List.foldl_append]

/-- Attaching a Markov kernel keeps the first marginal. -/
public theorem semiproduct_map_first {α β : Type} {source : Space α} {target : Space β}
    (measure : Measure source) (kernel : Kernel source target)
    (kernelFinite : Kernel.IsSFinite kernel)
    (markov : ∀ input, Measure.IsProbability (kernel input)) :
    (measure.semiproduct kernel kernelFinite).map Prod.fst (Space.first_measurable _ _) =
      measure := by
  apply Measure.ext
  intro set measurable
  have product : Set.preimage (Prod.fst : α × β → α) set = Set.product set Set.univ := by
    funext pair
    exact propext ⟨fun inside => ⟨inside, True.intro⟩, fun inside => inside.1⟩
  rw [Measure.map_apply _ _ _ measurable, product,
    Measure.semiproduct_apply_product _ _ _ measurable target.univ]
  have unit : (fun input => kernel input Set.univ) = fun _ => ENNReal.one :=
    funext fun input => (markov input).univ_eq_one
  rw [unit, lintegral_const, Measure.restrict_apply _ _ source.univ, ENNReal.one_mul]
  congr 1
  funext value
  exact propext ⟨fun inside => inside.2, fun inside => ⟨True.intro, inside⟩⟩

private theorem appendLaw_isProbability {law : Measure (Space.list borel)}
    (probability : Measure.IsProbability law) (row : Row) :
    Measure.IsProbability (appendLaw law row) := by
  apply Measure.IsProbability.map
  apply Measure.IsProbability.bind probability
  intro values
  change Measure.IsProbability ((row.kernel values).map (fun value => (values, value))
    (Kernel.pair_left_measurable values))
  exact Measure.IsProbability.map (row.kernel_isProbability values) _ _

/-- Every network's law is a probability measure. -/
public theorem Network.law_isProbability (network : Network) :
    Measure.IsProbability network.law := by
  unfold Network.law
  generalize network.rows = rows
  suffices ∀ (law : Measure (Space.list borel)), Measure.IsProbability law →
      Measure.IsProbability (rows.foldl appendLaw law) from
    this _ (Measure.IsProbability.dirac _ _)
  induction rows with
  | nil => exact fun law probability => probability
  | cons row rows induction =>
      exact fun law probability => induction _ (appendLaw_isProbability probability row)

/-- Dropping the last node marginalizes it. -/
public theorem Network.marginal_last (network : Network) (nonempty : 0 < network.length) :
    network.law.map List.dropLast dropLast_measurable = network.init.law := by
  have rowsNonempty : network.rows ≠ [] := List.length_pos_iff.mp nonempty
  obtain ⟨shaped, positive, rebuilt⟩ := network.append_init_last rowsNonempty
  have rebuiltLaw : network.law.map List.dropLast dropLast_measurable =
      (network.init.append _ shaped positive).law.map List.dropLast dropLast_measurable := by
    rw [rebuilt]
  rw [rebuiltLaw, Network.law_append, appendLaw, Measure.map_comp]
  have first : (fun pair : List Carrier × Carrier => (snoc pair).dropLast) = Prod.fst := by
    funext pair
    exact List.dropLast_concat
  rw [Measure.map_congr_function _ _ (Space.first_measurable _ _) first]
  exact semiproduct_map_first _ _ _ (Row.kernel_isProbability _)

/-! ### The density -/

/-- The product of the scalar conditionals of `rows`, the first at position `index`. -/
@[expose] public def conditionals : List Row → Nat → List Carrier → NNReal
  | [], _, _ => NNReal.one
  | row :: rows, index, values =>
      NNReal.mul (row.density values index) (conditionals rows (index + 1) values)

/-- The network's density against `listVolume`: the product of its conditionals
on lists of its length, and zero elsewhere. -/
@[expose] public def Network.density (network : Network) (values : List Carrier) : NNReal :=
  if values.length = network.length then conditionals network.rows 0 values else NNReal.zero

public theorem conditionals_measurable (rows : List Row) (index : Nat) :
    ENNRealMeasurable (Space.list borel) (fun values => ENNReal.finite
      (conditionals rows index values)) := by
  induction rows generalizing index with
  | nil =>
      simp only [conditionals]
      exact ENNRealMeasurable.constant _ _
  | cons row rows induction =>
      simp only [conditionals, ← ENNReal.finite_mul_finite]
      exact ENNRealMeasurable.mul (row.density_measurable index) (induction (index + 1))

public theorem Network.density_measurable (network : Network) :
    ENNRealMeasurable (Space.list borel) (fun values => ENNReal.finite
      (network.density values)) := by
  let branches : Nat → List Carrier → ENNReal := fun length current =>
    if length = network.length then ENNReal.finite (conditionals network.rows 0 current)
    else ENNReal.zero
  have equal : (fun values => ENNReal.finite (network.density values)) = fun values =>
      branches values.length values := by
    funext values
    unfold Network.density
    show _ = if values.length = network.length then _ else _
    split <;> rfl
  rw [equal]
  apply ENNRealMeasurable.of_measurableMap
  apply MeasurableMap.countable_piecewise (branches := branches)
  · intro length
    exact ListSpace.length_measurable borel (set := fun current => current = length) trivial
  · intro length
    show MeasurableMap _ _ (fun current => if length = network.length then _ else _)
    split
    · exact (conditionals_measurable network.rows 0).measurableMap
    · exact MeasurableMap.constant _ _ _

public theorem conditionals_append (rows : List Row) (row : Row) (index : Nat)
    (values : List Carrier) :
    conditionals (rows ++ [row]) index values =
      NNReal.mul (conditionals rows index values) (row.density values (index + rows.length)) := by
  induction rows generalizing index with
  | nil => simp [conditionals, NNReal.mul_one, NNReal.one_mul]
  | cons head rows induction =>
      simp only [List.cons_append, conditionals, induction, NNReal.mul_assoc, List.length_cons]
      rw [Nat.add_assoc, Nat.add_comm 1]

/-- Rows that read only coordinates of `values` do not see an appended coordinate. -/
public theorem conditionals_concat (rows : List Row) (index : Nat) (values : List Carrier)
    (value : Carrier)
    (reads : ∀ (position : Nat) (row : Row), rows[position]? = some row →
      row.coefficients.length ≤ values.length ∧ index + position < values.length) :
    conditionals rows index (values ++ [value]) = conditionals rows index values := by
  induction rows generalizing index with
  | nil => rfl
  | cons row rows induction =>
      obtain ⟨short, below⟩ := reads 0 row rfl
      have rest := induction (index + 1) (fun position current found => by
        have read := reads (position + 1) current found
        exact ⟨read.1, by omega⟩)
      simp only [conditionals, rest, Row.density, Row.mean, dot_append_right _ short,
        entry_append_left _ (by simpa using below)]

/-- The density of a network with one more node, at a list extended by one
coordinate: the old density times the new node's conditional. -/
public theorem Network.density_append (network : Network) (row : Row) (shaped positive)
    (pair : List Carrier × Carrier) :
    ENNReal.finite ((network.append row shaped positive).density (snoc pair)) =
      ENNReal.mul (row.pairDensity pair) (ENNReal.finite (network.density pair.1)) := by
  unfold Network.density Row.pairDensity
  simp only [Network.length_append, snoc, List.length_append, List.length_singleton,
    Nat.add_right_cancel_iff]
  split
  · rename_i counted
    rw [ENNReal.mul_comm, ENNReal.finite_mul_finite]
    congr 1
    change conditionals (network.rows ++ [row]) 0 (pair.1 ++ [pair.2]) = _
    rw [conditionals_append, conditionals_concat]
    · congr 1
      unfold Row.density Row.mean
      rw [Nat.zero_add]
      have long : row.coefficients.length ≤ pair.1.length := by
        rw [shaped, counted]
        exact Nat.le_refl _
      unfold Network.length at counted
      rw [dot_append_right _ long]
      rw [← counted, entry_concat_length]
    · intro position current found
      have bounded : position < network.rows.length := by
        rcases Nat.lt_or_ge position network.rows.length with below | above
        · exact below
        · rw [List.getElem?_eq_none above] at found
          cases found
      rw [network.triangular position current found]
      unfold Network.length at counted
      omega
  · rw [ENNReal.finite_mul_finite, NNReal.mul_zero]

/-- The law is the list volume weighted by the density. -/
public theorem Network.law_eq_withDensity (network : Network) :
    network.law = (listVolume network.length).withDensity
      (fun values => ENNReal.finite (network.density values)) := by
  induction network using Network.induction with
  | empty network empty =>
      have zeroLength : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      have unit : (fun values => ENNReal.finite (network.density values)) =
          fun values => if values.length = 0 then ENNReal.one else ENNReal.zero := by
        funext values
        unfold Network.density
        rw [zeroLength, empty]
        split <;> rfl
      unfold Network.law
      rw [empty, zeroLength, unit, List.foldl_nil]
      have almost : (listVolume 0).AEEq
          (fun values : List Carrier => if values.length = 0 then ENNReal.one else ENNReal.zero)
          (fun _ => ENNReal.one) := by
        apply Measure.NullSet.mono (listVolume_length_null 0)
        intro values different counted
        apply different
        show (if values.length = 0 then ENNReal.one else ENNReal.zero) = ENNReal.one
        rw [ite_eq_left counted]
      rw [Measure.withDensity_congr_ae almost, Measure.withDensity_one]
      rfl
  | append network row shaped positive induction =>
      rw [Network.law_append, appendLaw, induction, Network.length_append, listVolume_succ]
      have represents : ∀ values, row.kernel values =
          volume.withDensity (fun value => row.pairDensity (values, value)) := fun values =>
        Gaussian.law_eq_withDensity _ _ positive
      rw [Measure.semiproduct_withDensity_prod _ (network.density_measurable) volume volumeSFinite
        row.kernel row.kernelSFinite row.pairDensity_measurable represents]
      rw [← Measure.map_withDensity _ _ snoc_measurable
        (network.append row shaped positive).density_measurable]
      congr 1
      congr 1
      funext pair
      exact (network.density_append row shaped positive pair).symm

/-! ### Certified integrals: almost-everywhere congruence and the tower rule -/

section Certified

variable {α : Type} {space : Space α}

private theorem ofReal_le_positive {measure : Measure space} {integrand : α → Carrier}
    (parts : IntegralParts measure integrand) (x : α) :
    ENNReal.le (ENNReal.ofReal (integrand x)) (ENNReal.finite (parts.positive x)) := by
  rw [← ENNReal.ofReal_toReal_finite (parts.positive x)]
  apply ENNReal.ofReal_monotone
  rw [parts.decomposition x, sub_eq_add_neg]
  have dropped := add_le_add_left_iff (shift := (parts.positive x).toReal).mpr
    (neg_nonpositive_iff.mp (parts.negative x).property)
  rwa [add_zero] at dropped

private theorem positive_finite {measure : Measure space} {integrand : α → Carrier}
    (parts : IntegralParts measure integrand) :
    ENNReal.Finite (lintegral measure (fun x => ENNReal.ofReal (integrand x))) :=
  ENNReal.finite_of_le (lintegral_mono measure (ofReal_le_positive parts))
    (by rw [parts.positive_integral]; exact True.intro)

/-- A certified integral transfers to an integrand equal to it almost everywhere. -/
public theorem HasRealIntegral.congr_ae {measure : Measure space} {f g : α → Carrier}
    {value : Carrier} (integral : HasRealIntegral measure f value)
    (measurable : MeasurableMap space borel g) (equal : measure.AEEq f g) :
    HasRealIntegral measure g value := by
  obtain ⟨parts, same⟩ := integral
  have positiveEqual : lintegral measure (fun x => ENNReal.ofReal (f x)) =
      lintegral measure (fun x => ENNReal.ofReal (g x)) :=
    lintegral_congr_ae (Measure.NullSet.mono equal fun x different same =>
      different (by show ENNReal.ofReal (f x) = ENNReal.ofReal (g x); rw [same]))
  have negativeEqual : lintegral measure (fun x => ENNReal.ofReal (neg (f x))) =
      lintegral measure (fun x => ENNReal.ofReal (neg (g x))) :=
    lintegral_congr_ae (Measure.NullSet.mono equal fun x different same =>
      different (by show ENNReal.ofReal (neg (f x)) = ENNReal.ofReal (neg (g x)); rw [same]))
  have positiveFinite := positive_finite parts
  have negativeFinite := positive_finite parts.negParts
  have positiveFinite' : ENNReal.Finite (lintegral measure (fun x => ENNReal.ofReal (g x))) := by
    rw [← positiveEqual]; exact positiveFinite
  have negativeFinite' : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (neg (g x)))) := by
    rw [← negativeEqual]; exact negativeFinite
  let source := IntegralParts.canonical parts.measurable positiveFinite negativeFinite
  let target := IntegralParts.canonical measurable positiveFinite' negativeFinite'
  refine ⟨target, ?_⟩
  rw [← same, ← source.unique parts]
  have positiveMass : target.positiveMass = source.positiveMass := by
    apply ENNReal.finite_injective
    rw [← target.positive_integral, ← source.positive_integral]
    exact positiveEqual.symm
  have negativeMass : target.negativeMass = source.negativeMass := by
    apply ENNReal.finite_injective
    rw [← target.negative_integral, ← source.negative_integral]
    exact negativeEqual.symm
  unfold IntegralParts.value
  rw [positiveMass, negativeMass]

/-- A nonnegative measurable integrand whose lower integral is a nonnegative
real has that real as its certified integral. -/
public theorem hasRealIntegral_of_lintegral {measure : Measure space} {integrand : α → Carrier}
    (nonnegative : ∀ x, le zero (integrand x)) (measurable : MeasurableMap space borel integrand)
    {value : Carrier} (valueNonnegative : le zero value)
    (integral : lintegral measure (fun x => ENNReal.ofReal (integrand x)) = ENNReal.ofReal value) :
    HasRealIntegral measure integrand value := by
  refine ⟨{ positive := fun x => NNReal.ofReal (integrand x)
            negative := fun _ => NNReal.zero
            positive_measurable := ENNRealMeasurable.comp (map := ENNReal.ofReal)
              ofReal_measurable measurable
            negative_measurable := ENNRealMeasurable.constant _ _
            decomposition := fun x => by
              rw [NNReal.toReal_ofReal (nonnegative x), NNReal.toReal_zero, sub_zero]
            positiveMass := NNReal.ofReal value
            negativeMass := NNReal.zero
            positive_integral := integral
            negative_integral := lintegral_zero _ }, ?_⟩
  change sub (NNReal.ofReal value).toReal NNReal.zero.toReal = value
  rw [NNReal.toReal_ofReal valueNonnegative, NNReal.toReal_zero, sub_zero]

/-- The certified integral of a nonnegative integrand is nonnegative. -/
public theorem HasRealIntegral.nonnegative_value {measure : Measure space}
    {integrand : α → Carrier} {value : Carrier} (nonnegative : ∀ x, le zero (integrand x))
    (integral : HasRealIntegral measure integrand value) : le zero value := by
  have lower := HasRealIntegral.lintegral_ofReal nonnegative integral
  have lower' : lintegral measure (fun x => ENNReal.ofReal (integrand x)) =
      ENNReal.ofReal (NNReal.ofReal value).toReal := by
    rw [lower]
    change ENNReal.finite (NNReal.ofReal value) =
      ENNReal.finite (NNReal.ofReal (NNReal.ofReal value).toReal)
    rw [NNReal.ofReal_toReal]
  have parts := hasRealIntegral_of_lintegral nonnegative (HasRealIntegral.measurable integral)
    (NNReal.ofReal value).property lower'
  have equal := integral.unique parts
  rw [equal]
  exact (NNReal.ofReal value).property

end Certified

/-- A certified integral transfers along an equality of values. -/
public theorem HasRealIntegral.of_value_eq {α : Type} {space : Space α} {measure : Measure space}
    {integrand : α → Carrier} {left right : Carrier} (integral : HasRealIntegral measure integrand
      left)
    (equal : left = right) : HasRealIntegral measure integrand right :=
  equal ▸ integral

/-- The tower rule for a nonnegative integrand of a semiproduct: integrate the
kernel first, then the first measure. -/
public theorem HasRealIntegral.semiproduct {α β : Type} {source : Space α} {target : Space β}
    (measure : Measure source) (kernel : Kernel source target)
    (kernelFinite : Kernel.IsSFinite kernel) {integrand : α × β → Carrier}
    (nonnegative : ∀ pair, le zero (integrand pair))
    (measurable : MeasurableMap (Space.product source target) borel integrand)
    {inner : α → Carrier}
    (innerIntegral : ∀ x, HasRealIntegral (kernel x) (fun y => integrand (x, y)) (inner x))
    {value : Carrier} (outer : HasRealIntegral measure inner value) :
    HasRealIntegral (measure.semiproduct kernel kernelFinite) integrand value := by
  have innerNonnegative : ∀ x, le zero (inner x) := fun x =>
    HasRealIntegral.nonnegative_value (fun y => nonnegative (x, y)) (innerIntegral x)
  apply hasRealIntegral_of_lintegral nonnegative measurable
    (HasRealIntegral.nonnegative_value innerNonnegative outer)
  rw [lintegral_semiproduct _ _ _ (ENNRealMeasurable.comp (map := ENNReal.ofReal)
    ofReal_measurable measurable)]
  have pointwise : (fun x => lintegral (kernel x) (fun y => ENNReal.ofReal (integrand (x, y)))) =
      fun x => ENNReal.ofReal (inner x) :=
    funext fun x => HasRealIntegral.lintegral_ofReal (fun y => nonnegative (x, y)) (innerIntegral x)
  rw [pointwise]
  exact HasRealIntegral.lintegral_ofReal innerNonnegative outer

/-- A Gaussian integrates the square of an affine reading in closed form. -/
public theorem square_expectation (mean variance : Carrier) (positive : lt zero variance)
    (shift scale : Carrier) :
    HasRealIntegral (law mean variance)
      (fun y => mul (add shift (mul scale y)) (add shift (mul scale y)))
      (add (mul (add shift (mul scale mean)) (add shift (mul scale mean)))
        (mul (mul scale scale) variance)) := by
  have combined := HasRealIntegral.add (HasRealIntegral.add
    (HasRealIntegral.const (law_isProbability mean variance) (mul shift shift))
    (HasRealIntegral.smul (mean_expectation mean variance positive)
      (mul (selection.ofRat 2) (mul shift scale))))
    (HasRealIntegral.smul (second_moment_expectation mean variance positive) (mul scale scale))
  have value : add (add (mul shift shift) (mul (mul (selection.ofRat 2) (mul shift scale)) mean))
      (mul (mul scale scale) (add variance (mul mean mean))) =
      add (mul (add shift (mul scale mean)) (add shift (mul scale mean)))
        (mul (mul scale scale) variance) := by
    real_grind
  rw [value] at combined
  exact HasRealIntegral.congr combined fun y => by real_grind

/-! ### Finite sums over indices -/

/-- `Σ_{k<n} f k`. -/
@[expose] public def sumBelow : Nat → (Nat → Carrier) → Carrier
  | 0, _ => zero
  | count + 1, term => add (sumBelow count term) (term count)

public theorem sumBelow_congr {count : Nat} {left right : Nat → Carrier}
    (equal : ∀ index, index < count → left index = right index) :
    sumBelow count left = sumBelow count right := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change add (sumBelow count left) (left count) = add (sumBelow count right) (right count)
      rw [induction (fun index below => equal index (Nat.lt_succ_of_lt below)),
        equal count (Nat.lt_succ_self count)]

public theorem sumBelow_add (count : Nat) (left right : Nat → Carrier) :
    sumBelow count (fun index => add (left index) (right index)) =
      add (sumBelow count left) (sumBelow count right) := by
  induction count with
  | zero => exact (add_zero zero).symm
  | succ count induction =>
      change add (sumBelow count _) _ = add (add (sumBelow count left) _) (add
        (sumBelow count right) _)
      rw [induction]
      real_grind

public theorem sumBelow_mul_left (count : Nat) (scalar : Carrier) (term : Nat → Carrier) :
    sumBelow count (fun index => mul scalar (term index)) = mul scalar (sumBelow count term) := by
  induction count with
  | zero => exact (mul_zero scalar).symm
  | succ count induction =>
      change add (sumBelow count _) _ = mul scalar (add (sumBelow count term) _)
      rw [induction]
      real_grind

public theorem sumBelow_succ_left (count : Nat) (term : Nat → Carrier) :
    sumBelow (count + 1) term = add (term 0) (sumBelow count (fun index => term (index + 1))) := by
  induction count with
  | zero =>
      change add zero (term 0) = add (term 0) zero
      real_grind
  | succ count induction =>
      change add (sumBelow (count + 1) term) (term (count + 1)) =
        add (term 0) (add (sumBelow count (fun index => term (index + 1))) (term (count + 1)))
      rw [induction]
      real_grind

public theorem sumBelow_swap (outer inner : Nat) (term : Nat → Nat → Carrier) :
    sumBelow outer (fun first => sumBelow inner (fun second => term first second)) =
      sumBelow inner (fun second => sumBelow outer (fun first => term first second)) := by
  induction outer with
  | zero =>
      change zero = sumBelow inner (fun _ => zero)
      induction inner with
      | zero => rfl
      | succ inner induction =>
          change zero = add (sumBelow inner (fun _ => zero)) zero
          rw [← induction, add_zero]
  | succ outer induction =>
      change add (sumBelow outer _) _ = sumBelow inner (fun second => add _ _)
      rw [sumBelow_add, induction]

/-- A sum with one nonzero term. -/
public theorem sumBelow_single {count index : Nat} (below : index < count) (term : Nat → Carrier) :
    sumBelow count (fun current => if current = index then term current else
      zero) = term index := by
  induction count with
  | zero => cases below
  | succ count induction =>
      change add (sumBelow count _) (if count = index then term count else zero) = term index
      rcases Nat.lt_or_ge index count with inside | outside
      · rw [induction inside, ite_eq_right (Nat.ne_of_gt inside), add_zero]
      · have equal : index = count := by omega
        subst equal
        rw [ite_eq_left rfl]
        have vanish : sumBelow index (fun current => if current = index then term current else
          zero) =
            sumBelow index (fun _ => zero) :=
          sumBelow_congr fun current below => ite_eq_right (Nat.ne_of_lt below)
        have zeros : ∀ count, sumBelow count (fun _ : Nat => zero) = zero := by
          intro count
          induction count with
          | zero => rfl
          | succ count inner =>
              change add (sumBelow count _) zero = zero
              rw [inner, add_zero]
        rw [vanish, zeros, zero_add]

/-- The sum `Σ bⱼ xⱼ` as an index sum over the coefficients. Missing
coordinates read as zero, so this holds for every list of values. -/
public theorem dot_eq_sumBelow (coefficients values : List Carrier) :
    dot coefficients values =
      sumBelow coefficients.length (fun index => mul (entry coefficients index)
        (entry values index)) := by
  induction coefficients generalizing values with
  | nil => simp [sumBelow]
  | cons coefficient coefficients induction =>
      rw [dot_cons_left, induction, List.length_cons, sumBelow_succ_left]
      congr 1
      apply sumBelow_congr
      intro index _
      cases values <;> rfl

public theorem sumBelow_measurable (count : Nat) {term : Nat → List Carrier → Carrier}
    (measurable : ∀ index, MeasurableMap (Space.list borel) borel (term index)) :
    MeasurableMap (Space.list borel) borel (fun values => sumBelow count
      (fun index => term index values)) := by
  induction count with
  | zero => exact MeasurableMap.constant _ borel zero
  | succ count induction => exact measurable_add induction (measurable count)

/-! ### The moment recurrences, read by index -/

/-- The recurrences produce a mean of length `n` and an `n × n` covariance. -/
public theorem Network.shape (network : Network) :
    network.mean.length = network.length ∧ network.covariance.length = network.length ∧
      ∀ row ∈ network.covariance, row.length = network.length := by
  induction network using Network.induction with
  | empty network empty =>
      have zero : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      unfold Network.mean Network.covariance
      rw [empty, zero]
      exact ⟨rfl, rfl, fun _ member => nomatch member⟩
  | append network row shaped positive induction =>
      obtain ⟨meanLength, covarianceLength, rowLength⟩ := induction
      rw [Network.mean_append, Network.covariance_append, Network.length_append]
      refine ⟨by simp [meanAppend, meanLength], by simp [covarianceAppend, covarianceLength], ?_⟩
      intro current member
      simp only [covarianceAppend, List.mem_append, List.mem_map, List.mem_singleton] at member
      rcases member with ⟨old, oldMember, rfl⟩ | rfl
      · simp [rowLength old oldMember]
      · simp [covarianceLength]

/-- Entry `k` of the mean recurrence. -/
@[expose] public def Network.meanAt (network : Network) (index : Nat) : Carrier :=
  entry network.mean index

/-- Entry `(k, l)` of the covariance recurrence. -/
@[expose] public def Network.covarianceAt (network : Network) (first second : Nat) : Carrier :=
  entry (network.covariance.getD first []) second

/-- Column `k` of the covariance times the new row's coefficients: `(Σb)ₖ`. -/
@[expose] public def Network.cross (network : Network) (row : Row) (index : Nat) : Carrier :=
  sumBelow network.length (fun other =>
    mul (network.covarianceAt index other) (entry row.coefficients other))

section Recurrence

variable (network : Network) (row : Row) (shaped : row.coefficients.length = network.length)
  (positive : lt zero row.variance)

include shaped in
public theorem Network.meanAt_append_below {index : Nat} (below : index < network.length) :
    (network.append row shaped positive).meanAt index = network.meanAt index := by
  unfold Network.meanAt
  rw [Network.mean_append, meanAppend,
    entry_append_left _ (by rw [network.shape.1]; exact below)]

include shaped in
public theorem Network.meanAt_append_last :
    (network.append row shaped positive).meanAt network.length =
      add row.intercept (sumBelow network.length (fun index =>
        mul (entry row.coefficients index) (network.meanAt index))) := by
  unfold Network.meanAt
  rw [Network.mean_append, meanAppend, ← network.shape.1, entry_concat_length, dot_eq_sumBelow,
    shaped, network.shape.1]

private theorem getD_covariance {network : Network} {index : Nat} (below : index < network.length) :
    ∃ current, network.covariance.getD index [] = current ∧ current ∈ network.covariance := by
  have inside : index < network.covariance.length := by rw [network.shape.2.1]; exact below
  exact ⟨network.covariance[index], by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]; rfl,
    List.getElem_mem inside⟩

private theorem covariance_append_getD_below {index : Nat} (below : index < network.length) :
    (network.append row shaped positive).covariance.getD index [] =
      network.covariance.getD index [] ++
        [dot (network.covariance.getD index []) row.coefficients] := by
  have inside : index < network.covariance.length := by rw [network.shape.2.1]; exact below
  rw [Network.covariance_append, covarianceAppend, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using inside), List.getElem?_map,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  rfl

private theorem covariance_append_getD_last :
    (network.append row shaped positive).covariance.getD network.length [] =
      network.covariance.map (fun current => dot current row.coefficients) ++
        [add (dot row.coefficients
          (network.covariance.map
            (fun current => dot current row.coefficients))) row.variance] := by
  rw [Network.covariance_append, covarianceAppend, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp [network.shape.2.1])]
  simp [network.shape.2.1]

private theorem dot_covariance_row {index : Nat} (below : index < network.length) :
    dot (network.covariance.getD index []) row.coefficients = network.cross row index := by
  obtain ⟨current, found, member⟩ := getD_covariance below
  rw [dot_eq_sumBelow, found, network.shape.2.2 current member]
  unfold Network.cross Network.covarianceAt
  rw [found]

include shaped in
public theorem Network.covarianceAt_append_below {first second : Nat}
    (firstBelow : first < network.length) (secondBelow : second < network.length) :
    (network.append row shaped positive).covarianceAt first second =
      network.covarianceAt first second := by
  unfold Network.covarianceAt
  rw [covariance_append_getD_below network row shaped positive firstBelow]
  obtain ⟨current, found, member⟩ := getD_covariance firstBelow
  rw [found, entry_append_left _ (by rw [network.shape.2.2 current member]; exact secondBelow)]

include shaped in
public theorem Network.covarianceAt_append_right {index : Nat} (below : index < network.length) :
    (network.append row shaped positive).covarianceAt index network.length =
      network.cross row index := by
  unfold Network.covarianceAt
  rw [covariance_append_getD_below network row shaped positive below]
  obtain ⟨current, found, member⟩ := getD_covariance below
  have length := network.shape.2.2 current member
  rw [← dot_covariance_row network row below, found, ← length, entry_concat_length]

include shaped in
public theorem Network.covarianceAt_append_bottom {index : Nat} (below : index < network.length) :
    (network.append row shaped positive).covarianceAt network.length index =
      network.cross row index := by
  unfold Network.covarianceAt
  rw [covariance_append_getD_last network row shaped positive,
    entry_append_left _ (by simp [network.shape.2.1, below])]
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have inside : index < network.covariance.length := by rw [network.shape.2.1]; exact below
  rw [List.getElem?_eq_getElem inside]
  change dot network.covariance[index] row.coefficients = _
  rw [← dot_covariance_row network row below, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem inside]
  rfl

include shaped in
public theorem Network.covarianceAt_append_corner :
    (network.append row shaped positive).covarianceAt network.length network.length =
      add (sumBelow network.length (fun index =>
        mul (entry row.coefficients index) (network.cross row index))) row.variance := by
  unfold Network.covarianceAt
  have crossLength : (network.covariance.map (fun current => dot current row.coefficients)).length =
      network.length := by simp [network.shape.2.1]
  rw [covariance_append_getD_last network row shaped positive, ← crossLength,
    entry_concat_length, crossLength, dot_eq_sumBelow, shaped]
  congr 1
  apply sumBelow_congr
  intro index below
  congr 1
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have inside : index < network.covariance.length := by rw [network.shape.2.1]; exact below
  rw [List.getElem?_eq_getElem inside]
  change dot network.covariance[index] row.coefficients = _
  rw [← dot_covariance_row network row below, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem inside]
  rfl

end Recurrence

/-- The covariance recurrence is symmetric. -/
public theorem Network.covarianceAt_symmetric (network : Network) {first second : Nat}
    (firstBelow : first < network.length) (secondBelow : second < network.length) :
    network.covarianceAt first second = network.covarianceAt second first := by
  induction network using Network.induction generalizing first second with
  | empty network empty =>
      have zero : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      omega
  | append network row shaped positive induction =>
      rw [Network.length_append] at firstBelow secondBelow
      rcases Nat.lt_or_ge first network.length with firstInside | firstOutside <;>
        rcases Nat.lt_or_ge second network.length with secondInside | secondOutside
      · rw [Network.covarianceAt_append_below _ _ shaped _ firstInside secondInside,
          Network.covarianceAt_append_below _ _ shaped _ secondInside firstInside,
          induction firstInside secondInside]
      · have last : second = network.length := by omega
        subst last
        rw [Network.covarianceAt_append_right _ _ shaped _ firstInside,
          Network.covarianceAt_append_bottom _ _ shaped _ firstInside]
      · have last : first = network.length := by omega
        subst last
        rw [Network.covarianceAt_append_right _ _ shaped _ secondInside,
          Network.covarianceAt_append_bottom _ _ shaped _ secondInside]
      · have firstLast : first = network.length := by omega
        have secondLast : second = network.length := by omega
        rw [firstLast, secondLast]

/-! ### Linear and quadratic readings -/

private theorem sumBelow_linear (count : Nat) (scalar : Carrier) (left right : Nat → Carrier) :
    sumBelow count (fun index => add (left index) (mul scalar (right index))) =
      add (sumBelow count left) (mul scalar (sumBelow count right)) := by
  induction count with
  | zero =>
      change zero = add zero (mul scalar zero)
      real_grind
  | succ count induction =>
      change add (sumBelow count _) _ =
        add (add (sumBelow count left) _) (mul scalar (add (sumBelow count right) _))
      rw [induction]
      real_grind

private theorem sumBelow_quadratic (count : Nat) (first second : Carrier)
    (base cross crossed square : Nat → Carrier) :
    sumBelow count (fun index => add (add (base index)
        (mul first (add (cross index) (crossed index)))) (mul second (square index))) =
      add (add (sumBelow count base)
        (mul first (add (sumBelow count cross) (sumBelow count crossed))))
        (mul second (sumBelow count square)) := by
  induction count with
  | zero =>
      change zero = add (add zero (mul first (add zero zero))) (mul second zero)
      real_grind
  | succ count induction =>
      change add (sumBelow count _) _ = add (add (add (sumBelow count base) _)
        (mul first (add (add (sumBelow count cross) _) (add (sumBelow count crossed) _))))
        (mul second (add (sumBelow count square) _))
      rw [induction]
      real_grind

/-- The affine reading `α + Σ_{k<n} aₖ xₖ`. -/
@[expose] public def form (count : Nat) (shift : Carrier) (coefficient : Nat → Carrier)
    (values : List Carrier) : Carrier :=
  add shift (sumBelow count (fun index => mul (coefficient index) (entry values index)))

/-- The quadratic form `Σ_{k,l<n} aₖ aₗ Cₖₗ`. -/
@[expose] public def quadratic (count : Nat) (coefficient : Nat → Carrier)
    (covariance : Nat → Nat → Carrier) : Carrier :=
  sumBelow count (fun first => sumBelow count (fun second =>
    mul (mul (coefficient first) (coefficient second)) (covariance first second)))

/-- The bilinear form `Σ_{k,l<n} aₖ bₗ Cₖₗ`. -/
@[expose] public def bilinear (count : Nat) (left right : Nat → Carrier)
    (covariance : Nat → Nat → Carrier) : Carrier :=
  sumBelow count (fun first => sumBelow count (fun second =>
    mul (mul (left first) (right second)) (covariance first second)))

public theorem form_measurable (count : Nat) (shift : Carrier) (coefficient : Nat → Carrier) :
    MeasurableMap (Space.list borel) borel (form count shift coefficient) :=
  measurable_add (MeasurableMap.constant _ borel shift)
    (sumBelow_measurable count (term := fun index values =>
      mul (coefficient index) (entry values index))
      fun index => measurable_mul (MeasurableMap.constant _ borel (coefficient index))
        (entry_measurable index))

/-- Shifting the coefficients by a multiple of another expands the quadratic form. -/
public theorem quadratic_shift (count : Nat) (scalar : Carrier) (left right : Nat → Carrier)
    (covariance : Nat → Nat → Carrier) :
    quadratic count (fun index => add (left index) (mul scalar (right index))) covariance =
      add (add (quadratic count left covariance)
        (mul scalar (add (bilinear count left right covariance)
          (bilinear count right left covariance))))
        (mul (mul scalar scalar) (quadratic count right covariance)) := by
  unfold quadratic bilinear
  rw [← sumBelow_quadratic]
  apply sumBelow_congr
  intro first _
  rw [← sumBelow_quadratic]
  apply sumBelow_congr
  intro second _
  real_grind

/-- The bilinear form of a symmetric matrix is symmetric. -/
public theorem bilinear_comm (count : Nat) (left right : Nat → Carrier)
    {covariance : Nat → Nat → Carrier}
    (symmetric : ∀ first second, first < count → second < count →
      covariance first second = covariance second first) :
    bilinear count right left covariance = bilinear count left right covariance := by
  unfold bilinear
  rw [sumBelow_swap]
  apply sumBelow_congr
  intro first firstBelow
  apply sumBelow_congr
  intro second secondBelow
  rw [symmetric second first secondBelow firstBelow]
  real_grind

/-- Splitting the last index off a quadratic form. -/
public theorem quadratic_succ (count : Nat) (coefficient : Nat → Carrier)
    (covariance : Nat → Nat → Carrier) :
    quadratic (count + 1) coefficient covariance =
      add (add (quadratic count coefficient covariance)
        (add (sumBelow count (fun first =>
            mul (mul (coefficient first) (coefficient count)) (covariance first count)))
          (sumBelow count (fun second =>
            mul (mul (coefficient count) (coefficient second)) (covariance count second)))))
        (mul (mul (coefficient count) (coefficient count)) (covariance count count)) := by
  unfold quadratic
  change add (sumBelow count (fun first => add (sumBelow count _) _))
      (add (sumBelow count _) _) = _
  rw [sumBelow_add]
  real_grind

private theorem mul_sumBelow (scalar : Carrier) (count : Nat) (term : Nat → Carrier) :
    mul scalar (sumBelow count term) = sumBelow count (fun index => mul scalar (term index)) :=
  (sumBelow_mul_left count scalar term).symm

/-! ### Moments -/

/-- The law is carried by lists of the network's length. -/
public theorem Network.law_length_null (network : Network) :
    network.law (fun values => values.length ≠ network.length) = ENNReal.zero := by
  rw [network.law_eq_withDensity]
  exact Measure.NullSet.withDensity (listVolume_length_null network.length) _

/-- The square of every affine reading integrates to the square of the reading
at the mean plus the quadratic form of the covariance. This carries the first
and second moments of the law (`moments_eq`). -/
public theorem Network.square_form (network : Network) (shift : Carrier)
    (coefficient : Nat → Carrier) :
    HasRealIntegral network.law
      (fun values => mul (form network.length shift coefficient values)
        (form network.length shift coefficient values))
      (add (mul (form network.length shift coefficient network.mean)
          (form network.length shift coefficient network.mean))
        (quadratic network.length coefficient network.covarianceAt)) := by
  induction network using Network.induction generalizing shift coefficient with
  | empty network empty =>
      have vanishing : network.length = 0 := by
        unfold Network.length
        rw [empty]
        rfl
      have constant := HasRealIntegral.const network.law_isProbability (mul shift shift)
      rw [vanishing]
      unfold form quadratic
      change HasRealIntegral network.law
        (fun _ => mul (add shift zero) (add shift zero))
        (add (mul (add shift zero) (add shift zero)) zero)
      rw [add_zero, add_zero]
      exact constant
  | append network row shaped positive induction =>
      -- The conditional mean as an index sum.
      have meanSum : ∀ values, row.mean values =
          add row.intercept (sumBelow network.length (fun index =>
            mul (entry row.coefficients index) (entry values index))) := by
        intro values
        unfold Row.mean
        rw [dot_eq_sumBelow, shaped]
      -- Integrating the new node first leaves a square of the old nodes.
      have regrouped : ∀ values,
          add (form network.length shift coefficient values) (mul (coefficient network.length)
            (row.mean values)) =
            form network.length (add shift (mul
              (coefficient
                network.length) row.intercept)) (fun index => add (coefficient index) (mul
                  (coefficient network.length) (entry row.coefficients index))) values := by
        intro values
        unfold form
        rw [meanSum]
        have expanded : sumBelow network.length (fun index =>
            mul ((fun index => add (coefficient index) (mul (coefficient network.length)
              (entry row.coefficients index))) index) (entry values index)) =
            sumBelow network.length (fun index => add (mul (coefficient index) (entry values index))
              (mul (coefficient network.length) (mul (entry row.coefficients index)
                (entry values index)))) :=
          sumBelow_congr fun index _ => by
            show mul (add (coefficient index) (mul (coefficient network.length)
              (entry row.coefficients index))) _ = _
            real_grind
        rw [expanded, sumBelow_linear]
        real_grind
      have outer := HasRealIntegral.add (induction (add shift (mul
        (coefficient
          network.length) row.intercept)) (fun index => add (coefficient index) (mul
            (coefficient network.length) (entry row.coefficients index))))
        (HasRealIntegral.const network.law_isProbability (mul (mul (coefficient network.length)
          (coefficient network.length)) row.variance))
      have joint : HasRealIntegral (network.law.semiproduct row.kernel row.kernelSFinite)
          (fun pair : List Carrier × Carrier =>
            mul (add (form network.length shift coefficient pair.1) (mul
              (coefficient network.length) pair.2))
              (add (form network.length shift coefficient pair.1) (mul
                (coefficient network.length) pair.2)))
          (add (add (mul (form network.length (add shift (mul
            (coefficient
              network.length) row.intercept)) (fun index => add (coefficient index) (mul
                (coefficient network.length) (entry row.coefficients index))) network.mean)
              (form network.length (add shift (mul (coefficient network.length) row.intercept))
                (fun index => add (coefficient index) (mul (coefficient network.length)
                  (entry row.coefficients index))) network.mean))
            (quadratic network.length (fun index => add (coefficient index) (mul
              (coefficient network.length) (entry row.coefficients index))) network.covarianceAt))
            (mul (mul (coefficient network.length)
              (coefficient network.length)) row.variance)) := by
        apply HasRealIntegral.semiproduct _ _ _ (fun _ => mul_self_nonnegative _)
          (by measurability [form_measurable network.length shift coefficient])
          (fun values => square_expectation (row.mean values) row.variance positive
            (form network.length shift coefficient values) (coefficient network.length))
        refine HasRealIntegral.congr outer fun values => ?_
        show add _ _ = add (mul (add _ (mul (coefficient network.length) (row.mean values)))
          (add _ (mul (coefficient network.length) (row.mean values)))) _
        rw [regrouped]
      -- Push forward along appending, which agrees off a null set.
      have nullPairs : (network.law.semiproduct row.kernel row.kernelSFinite)
          (Set.preimage Prod.fst (Set.preimage (List.length (α := Carrier))
            (fun length => length ≠ network.length))) =
          ENNReal.zero := by
        rw [← Measure.map_apply _ Prod.fst (Space.first_measurable _ _)
          (ListSpace.length_measurable borel
            (set := fun length => length ≠ network.length) trivial),
          semiproduct_map_first _ _ _ row.kernel_isProbability]
        exact network.law_length_null
      have pushed := HasRealIntegral.map snoc_measurable
        (by measurability [form_measurable (network.length + 1) shift coefficient] :
          MeasurableMap (Space.list borel) borel (fun values =>
            mul (form (network.length + 1) shift coefficient values)
              (form (network.length + 1) shift coefficient values)))
        (HasRealIntegral.congr_ae joint
          (by measurability [form_measurable (network.length + 1) shift coefficient,
            snoc_measurable])
          (Measure.NullSet.mono nullPairs fun pair different counted => different (by
            have length : pair.1.length = network.length := counted
            have appended : form (network.length + 1) shift coefficient (snoc pair) =
                add (form network.length shift coefficient pair.1) (mul
                  (coefficient network.length) pair.2) := by
              unfold form snoc
              change add shift (add (sumBelow network.length _) (mul (coefficient network.length)
                (entry (pair.1 ++ [pair.2]) network.length))) = _
              rw [← length, entry_concat_length, length]
              have front : sumBelow network.length (fun index =>
                  mul (coefficient index) (entry (pair.1 ++ [pair.2]) index)) =
                  sumBelow network.length (fun index => mul (coefficient index)
                    (entry pair.1 index)) :=
                sumBelow_congr fun index below => by
                  rw [entry_append_left _ (by rw [length]; exact below)]
              rw [front]
              real_grind
            show _ = mul (form (network.length + 1) shift coefficient (snoc pair))
              (form (network.length + 1) shift coefficient (snoc pair))
            rw [appended])))
      rw [Network.law_append, Network.length_append]
      refine HasRealIntegral.of_value_eq pushed ?_
      -- The value: the recurrences of the appended network.
      have symmetric : ∀ first second, first < network.length → second < network.length →
          network.covarianceAt first second = network.covarianceAt second first :=
        fun _ _ firstBelow secondBelow =>
          network.covarianceAt_symmetric firstBelow secondBelow
      have meanValue : form (network.length + 1) shift coefficient
          (network.append row shaped positive).mean =
          add (form network.length shift coefficient network.mean)
            (mul (coefficient network.length) (add row.intercept (sumBelow network.length
              (fun index =>
              mul (entry row.coefficients index) (network.meanAt index))))) := by
        unfold form
        change add shift (add (sumBelow network.length _) (mul (coefficient network.length)
          ((network.append row shaped positive).meanAt network.length))) = _
        rw [Network.meanAt_append_last]
        have front : sumBelow network.length (fun index => mul (coefficient index)
            (entry (network.append row shaped positive).mean index)) =
            sumBelow network.length (fun index => mul (coefficient index)
              (entry network.mean index)) :=
          sumBelow_congr fun index below => by
            show mul _ ((network.append row shaped positive).meanAt index) =
              mul _ (network.meanAt index)
            rw [Network.meanAt_append_below _ _ shaped _ below]
        rw [front]
        real_grind
      have meanShift : add (form network.length shift coefficient network.mean)
          (mul (coefficient network.length) (add row.intercept (sumBelow network.length
            (fun index =>
            mul (entry row.coefficients index) (network.meanAt index))))) =
          form network.length (add shift (mul
            (coefficient
              network.length) row.intercept)) (fun index => add (coefficient index) (mul
                (coefficient network.length) (entry row.coefficients index))) network.mean := by
        refine Eq.trans ?_ (regrouped network.mean)
        rw [meanSum]
        rfl
      have crossSum : ∀ (left : Nat → Carrier),
          sumBelow network.length (fun index => mul (left index) (network.cross row index)) =
            bilinear network.length left (entry row.coefficients) network.covarianceAt := by
        intro left
        unfold bilinear Network.cross
        apply sumBelow_congr
        intro first _
        rw [mul_sumBelow]
        apply sumBelow_congr
        intro second _
        real_grind
      have quadraticValue : quadratic (network.length + 1) coefficient
          (network.append row shaped positive).covarianceAt =
          add (add (quadratic network.length coefficient network.covarianceAt)
            (mul (coefficient network.length) (add (bilinear network.length coefficient
              (entry row.coefficients) network.covarianceAt)
              (bilinear network.length coefficient (entry row.coefficients) network.covarianceAt))))
            (mul (mul (coefficient network.length) (coefficient network.length))
              (add (quadratic network.length
                (entry row.coefficients) network.covarianceAt) row.variance)) := by
        rw [quadratic_succ]
        have block : quadratic network.length coefficient (network.append row shaped
          positive).covarianceAt =
            quadratic network.length coefficient network.covarianceAt := by
          unfold quadratic
          apply sumBelow_congr
          intro first firstBelow
          apply sumBelow_congr
          intro second secondBelow
          rw [Network.covarianceAt_append_below _ _ shaped _ firstBelow secondBelow]
        have right : sumBelow network.length (fun first => mul (mul (coefficient first)
          (coefficient network.length))
            ((network.append row shaped positive).covarianceAt first network.length)) =
            mul (coefficient network.length) (bilinear network.length coefficient
              (entry row.coefficients) network.covarianceAt) := by
          rw [← crossSum, mul_sumBelow]
          apply sumBelow_congr
          intro first below
          rw [Network.covarianceAt_append_right _ _ shaped _ below]
          real_grind
        have bottom : sumBelow network.length (fun second => mul (mul (coefficient network.length)
          (coefficient second))
            ((network.append row shaped positive).covarianceAt network.length second)) =
            mul (coefficient network.length) (bilinear network.length coefficient
              (entry row.coefficients) network.covarianceAt) := by
          rw [← crossSum, mul_sumBelow]
          apply sumBelow_congr
          intro second below
          rw [Network.covarianceAt_append_bottom _ _ shaped _ below]
          real_grind
        have corner := Network.covarianceAt_append_corner network row shaped positive
        have slopeQuadratic : sumBelow network.length (fun index => mul
          (entry row.coefficients index)
            (network.cross row
              index)) = quadratic network.length (entry row.coefficients) network.covarianceAt := by
          rw [show (fun index => mul (entry row.coefficients index) (network.cross row index)) =
            (fun index => mul (entry row.coefficients index)
              (network.cross row index)) from rfl, crossSum]
          unfold bilinear quadratic
          rfl
        change add (add (quadratic network.length coefficient _) (add (sumBelow network.length
          (fun first =>
            mul (mul (coefficient first)
              (coefficient network.length)) _)) (sumBelow network.length (fun second =>
            mul (mul (coefficient network.length)
              (coefficient
                second)) _)))) (mul (mul (coefficient network.length)
                  (coefficient network.length)) _) = _
        rw [block, right, bottom, corner, slopeQuadratic]
        real_grind
      rw [meanValue, quadraticValue, meanShift, quadratic_shift,
        bilinear_comm network.length coefficient (entry row.coefficients) symmetric]
      real_grind

/-- The coordinate coefficients `k ↦ [k = i]`. -/
@[expose] public def unit (index current : Nat) : Carrier :=
  if current = index then one else zero

/-- Unit coefficients pick one term out of a sum. -/
public theorem sumBelow_unit {count index : Nat} (below : index < count) (term : Nat → Carrier) :
    sumBelow count (fun current => mul (unit index current) (term current)) = term index := by
  refine Eq.trans (sumBelow_congr fun current _ => ?_) (sumBelow_single below term)
  unfold unit
  by_cases same : current = index
  · rw [ite_eq_left same, ite_eq_left same]
    real_grind
  · rw [ite_eq_right same, ite_eq_right same]
    real_grind

/-- Unit coefficients read one entry of the bilinear form. -/
public theorem bilinear_unit {count first second : Nat} (firstBelow : first < count)
    (secondBelow : second < count) (covariance : Nat → Nat → Carrier) :
    bilinear count (unit first) (unit second) covariance = covariance first second := by
  unfold bilinear
  have inner : ∀ current, sumBelow count (fun other =>
      mul (mul (unit first current) (unit second other)) (covariance current other)) =
      mul (unit first current) (covariance current second) := by
    intro current
    refine Eq.trans ?_ (congrArg (mul (unit first current))
      (sumBelow_unit secondBelow (fun other => covariance current other)))
    rw [mul_sumBelow]
    apply sumBelow_congr
    intro other _
    real_grind
  refine Eq.trans (sumBelow_congr fun current _ => inner current) ?_
  exact sumBelow_unit firstBelow (fun current => covariance current second)

/-- A shifted unit reading is the shift plus one entry. -/
public theorem form_unit {count index : Nat} (below : index < count) (shift : Carrier)
    (values : List Carrier) :
    form count shift (unit index) values = add shift (entry values index) :=
  congrArg (add shift) (sumBelow_unit below (fun current => entry values current))

/-- The reading `xᵢ + xⱼ` through the coefficients `[k = i] + 1·[k = j]`. -/
public theorem form_pair {count first second : Nat} (firstBelow : first < count)
    (secondBelow : second < count) (values : List Carrier) :
    form count zero (fun current => add (unit first current) (mul one
      (unit second current))) values =
      add (entry values first) (entry values second) := by
  unfold form
  have split : sumBelow count (fun current =>
      mul (add (unit first current) (mul one (unit second current))) (entry values current)) =
      sumBelow count (fun current => add (mul (unit first current) (entry values current))
        (mul one (mul (unit second current) (entry values current)))) :=
    sumBelow_congr fun current _ => by real_grind
  rw [split, sumBelow_linear,
    sumBelow_unit firstBelow (fun current => entry values current),
    sumBelow_unit secondBelow (fun current => entry values current)]
  real_grind

/-- The law's first and second moments are the recurrences:
`E[xᵢ] = μᵢ` and `E[xᵢ xⱼ] = Cᵢⱼ + μᵢ μⱼ`. Both follow from `square_form`
by polarization, so no signed product integral is taken directly. -/
public theorem Network.moments_eq (network : Network) {first second : Nat}
    (firstBelow : first < network.length) (secondBelow : second < network.length) :
    HasRealIntegral network.law (fun values => entry values first) (network.meanAt first) ∧
      HasRealIntegral network.law (fun values => mul (entry values first) (entry values second))
        (add (network.covarianceAt first second)
          (mul (network.meanAt first) (network.meanAt second))) := by
  have half : mul (inverse (selection.ofRat 2)) (selection.ofRat 2) = one :=
    inverse_mul_cancel ofRat_two_nonzero
  constructor
  · -- `E[(1 + xᵢ)²] - E[xᵢ²] - 1 = 2 E[xᵢ]`.
    have combined := HasRealIntegral.smul (HasRealIntegral.sub
      (HasRealIntegral.sub (network.square_form one (unit first))
        (network.square_form zero (unit first)))
      (HasRealIntegral.const network.law_isProbability one)) (inverse (selection.ofRat 2))
    refine HasRealIntegral.of_value_eq (HasRealIntegral.congr combined fun values => ?_) ?_
    · show mul _ (sub (sub (mul (form network.length one (unit first) values)
          (form network.length one (unit first) values))
          (mul (form network.length zero (unit first) values)
            (form network.length zero (unit first) values))) one) = entry values first
      rw [form_unit firstBelow, form_unit firstBelow]
      real_grind
    · rw [form_unit firstBelow, form_unit firstBelow]
      unfold Network.meanAt
      real_grind
  · -- `E[(xᵢ + xⱼ)²] - E[xᵢ²] - E[xⱼ²] = 2 E[xᵢ xⱼ]`.
    have combined := HasRealIntegral.smul (HasRealIntegral.sub
      (HasRealIntegral.sub
        (network.square_form zero (fun current => add (unit first current) (mul one
          (unit second current))))
        (network.square_form zero (unit first)))
      (network.square_form zero (unit second))) (inverse (selection.ofRat 2))
    refine HasRealIntegral.of_value_eq (HasRealIntegral.congr combined fun values => ?_) ?_
    · show mul _ (sub (sub (mul (form network.length zero _ values)
      (form network.length zero _ values))
          (mul (form network.length zero (unit first) values) (form network.length zero
            (unit first) values)))
          (mul (form network.length zero (unit second) values) (form network.length zero
            (unit second) values))) =
        mul (entry values first) (entry values second)
      rw [form_pair firstBelow secondBelow, form_unit firstBelow, form_unit secondBelow]
      real_grind
    · have symmetric : ∀ left right, left < network.length → right < network.length →
          network.covarianceAt left right = network.covarianceAt right left :=
        fun _ _ leftBelow rightBelow => network.covarianceAt_symmetric leftBelow rightBelow
      rw [form_pair firstBelow secondBelow, form_unit firstBelow, form_unit secondBelow,
        quadratic_shift, bilinear_unit firstBelow secondBelow, bilinear_unit secondBelow firstBelow,
        show quadratic network.length (unit first) network.covarianceAt =
          network.covarianceAt first first from bilinear_unit firstBelow firstBelow _,
        show quadratic network.length (unit second) network.covarianceAt =
          network.covarianceAt second second from bilinear_unit secondBelow secondBelow _,
        symmetric second first secondBelow firstBelow]
      unfold Network.meanAt
      real_grind

end
end Problib.Analysis.Gaussian
