import Foundations.Probability.FiniteSet
import Foundations.Probability.NNRat

namespace Foundations.Probability

universe u v w

private def totalWeights {α : Type u} : List (α × NNRat) → NNRat
  | [] => 0
  | (_, weight) :: rest => weight + totalWeights rest

private def integralWeights {α : Type u} (integrand : α → NNRat) : List (α × NNRat) → NNRat
  | [] => 0
  | (value, weight) :: rest => weight * integrand value + integralWeights integrand rest

private def massWeights {α : Type u} [DecidableEq α] (point : α) : List (α × NNRat) → NNRat
  | [] => 0
  | (value, weight) :: rest =>
      (if value = point then weight else 0) + massWeights point rest

private def mapWeights {α : Type u} {β : Type v} (mapValue : α → β) :
    List (α × NNRat) → List (β × NNRat)
  | [] => []
  | (value, weight) :: rest => (mapValue value, weight) :: mapWeights mapValue rest

private def scaleWeights {α : Type u} (factor : NNRat) :
    List (α × NNRat) → List (α × NNRat)
  | [] => []
  | (value, weight) :: rest => (value, factor * weight) :: scaleWeights factor rest

private def reweightWeights {α : Type u} (factor : α → NNRat) :
    List (α × NNRat) → List (α × NNRat)
  | [] => []
  | (value, weight) :: rest => (value, weight * factor value) :: reweightWeights factor rest

structure FiniteMeasure (α : Type u) where
  weights : List (α × NNRat)
deriving Repr

namespace FiniteMeasure

def zero {α : Type u} : FiniteMeasure α :=
  ⟨[]⟩

instance {α : Type u} : Zero (FiniteMeasure α) where
  zero := zero

def dirac {α : Type u} (value : α) : FiniteMeasure α :=
  ⟨[(value, 1)]⟩

def add {α : Type u} (left right : FiniteMeasure α) : FiniteMeasure α :=
  ⟨left.weights ++ right.weights⟩

instance {α : Type u} : Add (FiniteMeasure α) where
  add := add

def scale {α : Type u} (factor : NNRat) (measure : FiniteMeasure α) : FiniteMeasure α :=
  ⟨scaleWeights factor measure.weights⟩

def reweight {α : Type u} (measure : FiniteMeasure α) (factor : α → NNRat) : FiniteMeasure α :=
  ⟨reweightWeights factor measure.weights⟩

def map {α : Type u} {β : Type v} (mapValue : α → β) (measure : FiniteMeasure α) :
    FiniteMeasure β :=
  ⟨mapWeights mapValue measure.weights⟩

private def bindWeights {α : Type u} {β : Type v} (kernel : α → FiniteMeasure β) :
    List (α × NNRat) → List (β × NNRat)
  | [] => []
  | (value, weight) :: rest =>
      scaleWeights weight (kernel value).weights ++ bindWeights kernel rest

def bind {α : Type u} {β : Type v} (measure : FiniteMeasure α)
    (kernel : α → FiniteMeasure β) : FiniteMeasure β :=
  ⟨bindWeights kernel measure.weights⟩

def product {α : Type u} {β : Type v} (left : FiniteMeasure α) (right : FiniteMeasure β) :
    FiniteMeasure (α × β) :=
  bind left fun leftValue => map (fun rightValue => (leftValue, rightValue)) right

def total {α : Type u} (measure : FiniteMeasure α) : NNRat :=
  totalWeights measure.weights

def integral {α : Type u} (measure : FiniteMeasure α) (integrand : α → NNRat) : NNRat :=
  integralWeights integrand measure.weights

def mass {α : Type u} [DecidableEq α] (measure : FiniteMeasure α) (point : α) : NNRat :=
  massWeights point measure.weights

def support {α : Type u} [DecidableEq α] (measure : FiniteMeasure α) : FiniteSet α :=
  FiniteSet.ofList (measure.weights.map Prod.fst)

def Equivalent {α : Type u} (left right : FiniteMeasure α) : Prop :=
  ∀ integrand, left.integral integrand = right.integral integrand

infix:50 " ≈ₘ " => Equivalent

theorem Equivalent.refl {α : Type u} (measure : FiniteMeasure α) :
    measure ≈ₘ measure := by
  intro integrand
  rfl

theorem Equivalent.symm {α : Type u} {left right : FiniteMeasure α}
    (equivalent : left ≈ₘ right) : right ≈ₘ left := by
  intro integrand
  exact (equivalent integrand).symm

theorem Equivalent.trans {α : Type u} {first second third : FiniteMeasure α}
    (firstSecond : first ≈ₘ second) (secondThird : second ≈ₘ third) : first ≈ₘ third := by
  intro integrand
  exact Eq.trans (firstSecond integrand) (secondThird integrand)

private theorem totalWeights_append {α : Type u}
    (left right : List (α × NNRat)) :
    totalWeights (left ++ right) = totalWeights left + totalWeights right := by
  induction left with
  | nil => simp [totalWeights]
  | cons head tail ih =>
      cases head
      simp [totalWeights, ih, NNRat.add_assoc]

private theorem totalWeights_map {α : Type u} {β : Type v} (mapValue : α → β)
    (weights : List (α × NNRat)) :
    totalWeights (mapWeights mapValue weights) = totalWeights weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [mapWeights, totalWeights, ih]

private theorem totalWeights_scale {α : Type u} (factor : NNRat)
    (weights : List (α × NNRat)) :
    totalWeights (scaleWeights factor weights) = factor * totalWeights weights := by
  induction weights with
  | nil => simp [scaleWeights, totalWeights]
  | cons head tail ih =>
      cases head
      simp [scaleWeights, totalWeights, ih, NNRat.mul_add]

private theorem integralWeights_append {α : Type u} (integrand : α → NNRat)
    (left right : List (α × NNRat)) :
    integralWeights integrand (left ++ right) =
      integralWeights integrand left + integralWeights integrand right := by
  induction left with
  | nil => simp [integralWeights]
  | cons head tail ih =>
      cases head
      simp [integralWeights, ih, NNRat.add_assoc]

private theorem integralWeights_scale {α : Type u} (factor : NNRat)
    (integrand : α → NNRat) (weights : List (α × NNRat)) :
    integralWeights integrand (scaleWeights factor weights) =
      factor * integralWeights integrand weights := by
  induction weights with
  | nil => simp [scaleWeights, integralWeights]
  | cons head tail ih =>
      cases head
      simp [scaleWeights, integralWeights, ih, NNRat.mul_add, NNRat.mul_assoc]

private theorem integralWeights_map {α : Type u} {β : Type v} (mapValue : α → β)
    (integrand : β → NNRat) (weights : List (α × NNRat)) :
    integralWeights integrand (mapWeights mapValue weights) =
      integralWeights (fun value => integrand (mapValue value)) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [mapWeights, integralWeights, ih]

private theorem integralWeights_reweight {α : Type u} (factor integrand : α → NNRat)
    (weights : List (α × NNRat)) :
    integralWeights integrand (reweightWeights factor weights) =
      integralWeights (fun value => factor value * integrand value) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [reweightWeights, integralWeights, ih, NNRat.mul_assoc]

private theorem totalWeights_reweight {α : Type u} (factor : α → NNRat)
    (weights : List (α × NNRat)) :
    totalWeights (reweightWeights factor weights) = integralWeights factor weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [reweightWeights, totalWeights, integralWeights, ih]

private theorem integralWeights_congr {α : Type u} (weights : List (α × NNRat))
    {left right : α → NNRat} (equal : ∀ value, left value = right value) :
    integralWeights left weights = integralWeights right weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [integralWeights]
          rw [equal value, ih]

private theorem integralWeights_one {α : Type u} (weights : List (α × NNRat)) :
    integralWeights (fun _ => 1) weights = totalWeights weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [integralWeights, totalWeights, ih]

private theorem integralWeights_zero {α : Type u} (weights : List (α × NNRat)) :
    integralWeights (fun _ => 0) weights = 0 := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [integralWeights, ih]

private theorem integralWeights_zero_on_values {α : Type u}
    (integrand : α → NNRat) (weights : List (α × NNRat))
    (zero : ∀ value, value ∈ weights.map Prod.fst → integrand value = 0) :
    integralWeights integrand weights = 0 := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          have headZero : integrand value = 0 := zero value (by simp)
          have tailZero : ∀ tailValue, tailValue ∈ tail.map Prod.fst →
              integrand tailValue = 0 := by
            intro tailValue member
            exact zero tailValue (by simp [member])
          simp [integralWeights, headZero, ih tailZero]

private theorem integralWeights_mul_left {α : Type u} (constant : NNRat)
    (integrand : α → NNRat) (weights : List (α × NNRat)) :
    integralWeights (fun value => constant * integrand value) weights =
      constant * integralWeights integrand weights := by
  induction weights with
  | nil => simp [integralWeights]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [integralWeights]
          rw [ih, NNRat.mul_add]
          have headEqual : weight * (constant * integrand value) =
              constant * (weight * integrand value) := by
            rw [← NNRat.mul_assoc, NNRat.mul_comm weight constant, NNRat.mul_assoc]
          rw [headEqual]

private theorem integralWeights_add_functions {α : Type u}
    (left right : α → NNRat) (weights : List (α × NNRat)) :
    integralWeights (fun value => left value + right value) weights =
      integralWeights left weights + integralWeights right weights := by
  induction weights with
  | nil => simp [integralWeights]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [integralWeights]
          rw [NNRat.mul_add, ih, NNRat.add_add_add_comm]

private theorem integralWeights_swap {α : Type u} {β : Type v}
    (left : List (α × NNRat)) (right : List (β × NNRat))
    (integrand : α → β → NNRat) :
    integralWeights (fun leftValue => integralWeights (integrand leftValue) right) left =
      integralWeights (fun rightValue =>
        integralWeights (fun leftValue => integrand leftValue rightValue) left) right := by
  induction left with
  | nil =>
      exact (integralWeights_zero right).symm
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp only [integralWeights]
          rw [integralWeights_add_functions, integralWeights_mul_left, ih]

private theorem massWeights_append {α : Type u} [DecidableEq α] (point : α)
    (left right : List (α × NNRat)) :
    massWeights point (left ++ right) = massWeights point left + massWeights point right := by
  induction left with
  | nil => simp [massWeights]
  | cons head tail ih =>
      cases head
      simp [massWeights, ih, NNRat.add_assoc]

private theorem massWeights_scale {α : Type u} [DecidableEq α] (point : α)
    (factor : NNRat) (weights : List (α × NNRat)) :
    massWeights point (scaleWeights factor weights) = factor * massWeights point weights := by
  induction weights with
  | nil => simp [scaleWeights, massWeights]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          by_cases equal : value = point
          · simp [scaleWeights, massWeights, equal, ih, NNRat.mul_add]
          · simp [scaleWeights, massWeights, equal, ih]

private theorem massWeights_reweight {α : Type u} [DecidableEq α] (point : α)
    (factor : α → NNRat) (weights : List (α × NNRat)) :
    massWeights point (reweightWeights factor weights) =
      massWeights point weights * factor point := by
  induction weights with
  | nil => simp [reweightWeights, massWeights]
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          by_cases equal : value = point
          · subst equal
            simp [reweightWeights, massWeights, ih, NNRat.add_mul]
          · simp [reweightWeights, massWeights, equal, ih]

private theorem massWeights_map {α : Type u} {β : Type v} [DecidableEq β]
    (mapValue : α → β) (point : β) (weights : List (α × NNRat)) :
    massWeights point (mapWeights mapValue weights) =
      integralWeights (fun value => if mapValue value = point then 1 else 0) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          by_cases equal : mapValue value = point
          · simp [mapWeights, massWeights, integralWeights, equal, ih]
          · simp [mapWeights, massWeights, integralWeights, equal, ih]

private theorem massWeights_eq_integralIndicator {α : Type u} [DecidableEq α]
    (point : α) (weights : List (α × NNRat)) :
    massWeights point weights =
      integralWeights (fun value => if value = point then 1 else 0) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          by_cases equal : value = point
          · simp [massWeights, integralWeights, equal, ih]
          · simp [massWeights, integralWeights, equal, ih]

private theorem massWeights_zeroOutside {α : Type u} [DecidableEq α]
    (point : α) (weights : List (α × NNRat))
    (absent : point ∉ weights.map Prod.fst) : massWeights point weights = 0 := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          have unequal : value ≠ point := by
            intro equal
            apply absent
            simp [equal]
          have tailAbsent : point ∉ tail.map Prod.fst := by
            intro present
            apply absent
            simp [present]
          simp [massWeights, unequal, ih tailAbsent]

private theorem integralWeights_bind {α : Type u} {β : Type v}
    (kernel : α → FiniteMeasure β) (integrand : β → NNRat)
    (weights : List (α × NNRat)) :
    integralWeights integrand (bindWeights kernel weights) =
      integralWeights (fun value => (kernel value).integral integrand) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp [bindWeights, integralWeights, integral, integralWeights_append,
            integralWeights_scale, ih]

private theorem totalWeights_bind {α : Type u} {β : Type v}
    (kernel : α → FiniteMeasure β) (weights : List (α × NNRat)) :
    totalWeights (bindWeights kernel weights) =
      integralWeights (fun value => (kernel value).total) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp [bindWeights, total, integralWeights, totalWeights_append,
            totalWeights_scale, ih]

private theorem massWeights_bind {α : Type u} {β : Type v} [DecidableEq β]
    (kernel : α → FiniteMeasure β) (point : β) (weights : List (α × NNRat)) :
    massWeights point (bindWeights kernel weights) =
      integralWeights (fun value => (kernel value).mass point) weights := by
  induction weights with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk value weight =>
          simp [bindWeights, integralWeights, mass, massWeights_append, massWeights_scale, ih]

@[simp] theorem total_zero {α : Type u} : (0 : FiniteMeasure α).total = 0 := rfl

@[simp] theorem total_dirac {α : Type u} (value : α) : (dirac value).total = 1 := by
  simp [dirac, total, totalWeights]

theorem total_add {α : Type u} (left right : FiniteMeasure α) :
    (left + right).total = left.total + right.total :=
  totalWeights_append left.weights right.weights

theorem total_scale {α : Type u} (factor : NNRat) (measure : FiniteMeasure α) :
    (scale factor measure).total = factor * measure.total :=
  totalWeights_scale factor measure.weights

theorem total_map {α : Type u} {β : Type v} (mapValue : α → β) (measure : FiniteMeasure α) :
    (map mapValue measure).total = measure.total :=
  totalWeights_map mapValue measure.weights

theorem total_reweight {α : Type u} (measure : FiniteMeasure α) (factor : α → NNRat) :
    (reweight measure factor).total = measure.integral factor :=
  totalWeights_reweight factor measure.weights

theorem total_bind {α : Type u} {β : Type v} (measure : FiniteMeasure α)
    (kernel : α → FiniteMeasure β) :
    (bind measure kernel).total = measure.integral fun value => (kernel value).total :=
  totalWeights_bind kernel measure.weights

@[simp] theorem integral_zero {α : Type u} (integrand : α → NNRat) :
    (0 : FiniteMeasure α).integral integrand = 0 := rfl

@[simp] theorem integral_dirac {α : Type u} (value : α) (integrand : α → NNRat) :
    (dirac value).integral integrand = integrand value := by
  simp [dirac, integral, integralWeights]

theorem integral_add {α : Type u} (left right : FiniteMeasure α) (integrand : α → NNRat) :
    (left + right).integral integrand = left.integral integrand + right.integral integrand :=
  integralWeights_append integrand left.weights right.weights

theorem integral_scale {α : Type u} (factor : NNRat) (measure : FiniteMeasure α)
    (integrand : α → NNRat) :
    (scale factor measure).integral integrand = factor * measure.integral integrand :=
  integralWeights_scale factor integrand measure.weights

theorem integral_map {α : Type u} {β : Type v} (mapValue : α → β)
    (measure : FiniteMeasure α) (integrand : β → NNRat) :
    (map mapValue measure).integral integrand =
      measure.integral fun value => integrand (mapValue value) :=
  integralWeights_map mapValue integrand measure.weights

theorem integral_reweight {α : Type u} (measure : FiniteMeasure α)
    (factor integrand : α → NNRat) :
    (reweight measure factor).integral integrand =
      measure.integral fun value => factor value * integrand value :=
  integralWeights_reweight factor integrand measure.weights

theorem integral_bind {α : Type u} {β : Type v} (measure : FiniteMeasure α)
    (kernel : α → FiniteMeasure β) (integrand : β → NNRat) :
    (bind measure kernel).integral integrand =
      measure.integral fun value => (kernel value).integral integrand :=
  integralWeights_bind kernel integrand measure.weights

theorem integral_congr {α : Type u} (measure : FiniteMeasure α)
    {left right : α → NNRat} (equal : ∀ value, left value = right value) :
    measure.integral left = measure.integral right :=
  integralWeights_congr measure.weights equal

theorem integral_one {α : Type u} (measure : FiniteMeasure α) :
    measure.integral (fun _ => 1) = measure.total :=
  integralWeights_one measure.weights

theorem integral_zero_function {α : Type u} (measure : FiniteMeasure α) :
    measure.integral (fun _ => 0) = 0 :=
  integralWeights_zero measure.weights

theorem integral_zero_of_zero_on_support {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (integrand : α → NNRat)
    (zero : ∀ value, value ∈ measure.support → integrand value = 0) :
    measure.integral integrand = 0 := by
  apply integralWeights_zero_on_values
  intro value member
  apply zero value
  simpa [support] using member

theorem integral_mul_left {α : Type u} (measure : FiniteMeasure α)
    (constant : NNRat) (integrand : α → NNRat) :
    measure.integral (fun value => constant * integrand value) =
      constant * measure.integral integrand :=
  integralWeights_mul_left constant integrand measure.weights

theorem integral_swap {α : Type u} {β : Type v}
    (left : FiniteMeasure α) (right : FiniteMeasure β)
    (integrand : α → β → NNRat) :
    left.integral (fun leftValue => right.integral (integrand leftValue)) =
      right.integral (fun rightValue =>
        left.integral (fun leftValue => integrand leftValue rightValue)) :=
  integralWeights_swap left.weights right.weights integrand

@[simp] theorem mass_zero {α : Type u} [DecidableEq α] (point : α) :
    (0 : FiniteMeasure α).mass point = 0 := rfl

@[simp] theorem mass_dirac {α : Type u} [DecidableEq α] (value point : α) :
    (dirac value).mass point = if value = point then 1 else 0 := by
  simp [dirac, mass, massWeights]

theorem mass_add {α : Type u} [DecidableEq α] (left right : FiniteMeasure α)
    (point : α) : (left + right).mass point = left.mass point + right.mass point :=
  massWeights_append point left.weights right.weights

theorem mass_scale {α : Type u} [DecidableEq α] (factor : NNRat)
    (measure : FiniteMeasure α) (point : α) :
    (scale factor measure).mass point = factor * measure.mass point :=
  massWeights_scale point factor measure.weights

theorem mass_reweight {α : Type u} [DecidableEq α] (measure : FiniteMeasure α)
    (factor : α → NNRat) (point : α) :
    (reweight measure factor).mass point = measure.mass point * factor point :=
  massWeights_reweight point factor measure.weights

theorem mass_map {α : Type u} {β : Type v} [DecidableEq β] (mapValue : α → β)
    (measure : FiniteMeasure α) (point : β) :
    (map mapValue measure).mass point =
      measure.integral fun value => if mapValue value = point then 1 else 0 :=
  massWeights_map mapValue point measure.weights

theorem mass_bind {α : Type u} {β : Type v} [DecidableEq β]
    (measure : FiniteMeasure α) (kernel : α → FiniteMeasure β) (point : β) :
    (bind measure kernel).mass point =
      measure.integral fun value => (kernel value).mass point :=
  massWeights_bind kernel point measure.weights

theorem mass_eq_integral_indicator {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (point : α) :
    measure.mass point = measure.integral fun value => if value = point then 1 else 0 :=
  massWeights_eq_integralIndicator point measure.weights

theorem Equivalent.mass_eq {α : Type u} [DecidableEq α]
    {left right : FiniteMeasure α} (equivalent : left ≈ₘ right) (point : α) :
    left.mass point = right.mass point := by
  rw [mass_eq_integral_indicator, mass_eq_integral_indicator]
  exact equivalent fun value => if value = point then 1 else 0

theorem mass_zero_outside_support {α : Type u} [DecidableEq α]
    (measure : FiniteMeasure α) (point : α) (absent : point ∉ measure.support) :
    measure.mass point = 0 := by
  apply massWeights_zeroOutside point measure.weights
  intro present
  exact absent ((FiniteSet.mem_ofList (value := point)
    (values := measure.weights.map Prod.fst)).2 present)

theorem mass_map_injective {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (mapValue : α → β) (injective : ∀ {left right}, mapValue left = mapValue right → left = right)
    (measure : FiniteMeasure α) (point : α) :
    (map mapValue measure).mass (mapValue point) = measure.mass point := by
  rw [mass_map, mass_eq_integral_indicator]
  apply integral_congr
  intro value
  by_cases equal : value = point
  · subst equal
    simp
  · have imagesUnequal : mapValue value ≠ mapValue point := by
      intro imagesEqual
      exact equal (injective imagesEqual)
    simp [equal, imagesUnequal]

theorem mass_map_no_preimage {α : Type u} {β : Type v} [DecidableEq β]
    (mapValue : α → β) (measure : FiniteMeasure α) (point : β)
    (absent : ∀ value, mapValue value ≠ point) :
    (map mapValue measure).mass point = 0 := by
  rw [mass_map]
  calc
    measure.integral (fun value => if mapValue value = point then 1 else 0) =
        measure.integral (fun _ => 0) := by
          apply integral_congr
          intro value
          simp [absent value]
    _ = 0 := integral_zero_function measure

theorem Equivalent.map {α : Type u} {β : Type v}
    {left right : FiniteMeasure α} (equivalent : left ≈ₘ right)
    (transform : α → β) : map transform left ≈ₘ map transform right := by
  intro integrand
  rw [integral_map, integral_map]
  exact equivalent fun value => integrand (transform value)

theorem Equivalent.bind {α : Type u} {β : Type v}
    {left right : FiniteMeasure α} {leftKernel rightKernel : α → FiniteMeasure β}
    (measures : left ≈ₘ right)
    (kernels : ∀ value, leftKernel value ≈ₘ rightKernel value) :
    bind left leftKernel ≈ₘ bind right rightKernel := by
  intro integrand
  rw [integral_bind, integral_bind]
  calc
    left.integral (fun value => (leftKernel value).integral integrand) =
        left.integral (fun value => (rightKernel value).integral integrand) := by
      apply integral_congr
      intro value
      exact kernels value integrand
    _ = right.integral (fun value => (rightKernel value).integral integrand) :=
      measures fun value => (rightKernel value).integral integrand

/-- Bind transport when the right-hand measure is a mapped canonical source.
Only kernels at points in that image need a proof. -/
theorem Equivalent.bind_mapped_source
    {α : Type u} {β : Type v} {γ : Type w}
    {left : FiniteMeasure β} {source : FiniteMeasure α}
    (encode : α → β)
    {leftKernel : β → FiniteMeasure γ}
    {sourceKernel : α → FiniteMeasure γ}
    (measures : left ≈ₘ FiniteMeasure.map encode source)
    (kernels : ∀ value,
      leftKernel (encode value) ≈ₘ sourceKernel value) :
    FiniteMeasure.bind left leftKernel ≈ₘ
      FiniteMeasure.bind source sourceKernel := by
  intro integrand
  rw [integral_bind, integral_bind]
  calc
    left.integral (fun value => (leftKernel value).integral integrand) =
        (FiniteMeasure.map encode source).integral
          (fun value => (leftKernel value).integral integrand) :=
      measures _
    _ = source.integral (fun value =>
          (leftKernel (encode value)).integral integrand) :=
      integral_map encode source _
    _ = source.integral (fun value =>
          (sourceKernel value).integral integrand) := by
      apply integral_congr
      intro value
      exact kernels value integrand

theorem map_id {α : Type u} (measure : FiniteMeasure α) :
    map (fun value => value) measure ≈ₘ measure := by
  intro integrand
  rw [integral_map]

theorem map_comp {α : Type u} {β : Type v} {γ : Type w}
    (first : α → β) (second : β → γ) (measure : FiniteMeasure α) :
    map second (map first measure) ≈ₘ map (fun value => second (first value)) measure := by
  intro integrand
  rw [integral_map, integral_map, integral_map]

theorem bind_dirac_left {α : Type u} {β : Type v}
    (value : α) (kernel : α → FiniteMeasure β) :
    bind (dirac value) kernel ≈ₘ kernel value := by
  intro integrand
  rw [integral_bind, integral_dirac]

theorem bind_dirac_right {α : Type u} (measure : FiniteMeasure α) :
    bind measure dirac ≈ₘ measure := by
  intro integrand
  rw [integral_bind]
  apply integral_congr
  intro value
  exact integral_dirac value integrand

theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (measure : FiniteMeasure α) (first : α → FiniteMeasure β)
    (second : β → FiniteMeasure γ) :
    bind (bind measure first) second ≈ₘ
      bind measure (fun value => bind (first value) second) := by
  intro integrand
  rw [integral_bind, integral_bind, integral_bind]
  apply integral_congr
  intro value
  exact (integral_bind (first value) second integrand).symm

theorem bind_commute {α : Type u} {β : Type v} {γ : Type w}
    (left : FiniteMeasure α) (right : FiniteMeasure β)
    (kernel : α → β → FiniteMeasure γ) :
    bind left (fun leftValue => bind right (kernel leftValue)) ≈ₘ
      bind right (fun rightValue => bind left (fun leftValue =>
        kernel leftValue rightValue)) := by
  intro integrand
  rw [integral_bind, integral_bind]
  calc
    left.integral (fun leftValue =>
        (bind right (kernel leftValue)).integral integrand) =
        left.integral (fun leftValue => right.integral fun rightValue =>
          (kernel leftValue rightValue).integral integrand) := by
      apply integral_congr
      intro leftValue
      rw [integral_bind]
    _ = right.integral (fun rightValue => left.integral fun leftValue =>
        (kernel leftValue rightValue).integral integrand) :=
      integral_swap left right fun leftValue rightValue =>
        (kernel leftValue rightValue).integral integrand
    _ = right.integral (fun rightValue =>
        (bind left (fun leftValue => kernel leftValue rightValue)).integral integrand) := by
      apply integral_congr
      intro rightValue
      rw [integral_bind]

end FiniteMeasure

end Foundations.Probability
