import Problib.Measure.Kernel.Iteration.Minorization
import Problib.Probability.Finite.Interpretation
import Problib.Probability.Finite.Example
import Problib.Real.Extended.Lattice
import Problib.FiniteEnumeration

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real Problib.Probability

universe u
variable {α : Type u} [DecidableEq α]

private def covered (values : List α)
    (event : Set α) : Set α :=
  fun value => event value ∧ value ∈ values

omit [DecidableEq α] in
private theorem finite_singletons_determine_measure
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (first second : Measure (Space.discrete α))
    (singletons : ∀ point, first (Set.singleton point) =
      second (Set.singleton point)) : first = second := by
  have onList : ∀ values : List α, values.Nodup →
      ∀ event : Set α, first (covered values event) =
        second (covered values event) := by
    intro values
    induction values with
    | nil =>
        intro _ event
        have empty : covered [] event = Set.empty := by
          apply Set.ext
          intro value
          simp [covered, Set.empty]
        rw [empty]
        rw [first.empty_apply, second.empty_apply]
    | cons head tail induction =>
        intro nodup event
        have facts := List.nodup_cons.mp nodup
        by_cases member : event head
        · have split : covered (head :: tail) event =
              Set.union (Set.singleton head) (covered tail event) := by
            apply Set.ext
            intro value
            simp only [covered, Set.union, Set.singleton, List.mem_cons]
            constructor
            · rintro ⟨inEvent, equal | inTail⟩
              · exact Or.inl equal
              · exact Or.inr ⟨inEvent, inTail⟩
            · intro either
              rcases either with equal | ⟨inEvent, inTail⟩
              · subst value
                exact ⟨member, Or.inl rfl⟩
              · exact ⟨inEvent, Or.inr inTail⟩
          have disjoint : Set.Disjoint (Set.singleton head)
              (covered tail event) := by
            intro value equal inTail
            subst value
            exact facts.1 inTail.2
          rw [split,
            first.union_disjoint (Space.discrete_measurable _)
              (Space.discrete_measurable _) disjoint,
            second.union_disjoint (Space.discrete_measurable _)
              (Space.discrete_measurable _) disjoint,
            singletons head, induction facts.2 event]
        · have split : covered (head :: tail) event = covered tail event := by
            apply Set.ext
            intro value
            simp only [covered, List.mem_cons]
            constructor
            · rintro ⟨inEvent, equal | inTail⟩
              · subst value
                exact False.elim (member inEvent)
              · exact ⟨inEvent, inTail⟩
            · rintro ⟨inEvent, inTail⟩
              exact ⟨inEvent, Or.inr inTail⟩
          rw [split]
          exact induction facts.2 event
  apply Measure.ext
  intro event _
  have equal := onList enumeration
    (listed.nodup) event
  have cover : covered enumeration event = event := by
    apply Set.ext
    intro value
    simp [covered, listed.complete value]
  rwa [cover] at equal

/-- Sum a rational row over an explicit finite enumeration. -/
def matrixSum (enumeration : List α) (term : α → NNRat) : NNRat :=
  enumeration.foldr (fun index total => term index + total) 0

private def tableFromList (values : List α)
    (row : α → NNRat) : FiniteMeasure α :=
  values.foldr (fun value total =>
    FiniteMeasure.scale (row value) (FiniteMeasure.dirac value) + total) 0

private def tableFromRows
    (enumeration : List α)
    (rows : α → α → NNRat) (input : α) :
    FiniteMeasure α :=
  tableFromList enumeration (rows input)

omit [DecidableEq α] in
private theorem tableFromList_total
    (values : List α) (row : α → NNRat) :
    (tableFromList values row).total =
      values.foldr (fun value total => row value + total) 0 := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      change (FiniteMeasure.scale (row head) (FiniteMeasure.dirac head) +
        tableFromList tail row).total = row head +
          tail.foldr (fun value total => row value + total) 0
      rw [FiniteMeasure.total_add,
        FiniteMeasure.total_scale, FiniteMeasure.total_dirac,
        NNRat.mul_one, induction]

omit [DecidableEq α] in
private theorem tableFromRows_total
    (enumeration : List α)
    (rows : α → α → NNRat) (input : α) :
    (tableFromRows enumeration rows input).total = matrixSum enumeration (rows input) :=
  tableFromList_total enumeration (rows input)

private theorem list_sum_indicator_absent
    (values : List α) (target : α)
    (row : α → NNRat) (absent : target ∉ values) :
    values.foldr (fun value total =>
      (if value = target then row value else 0) + total) 0 = 0 := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headUnequal : head ≠ target := by
        intro equal
        exact absent (by simp [equal])
      have tailAbsent : target ∉ tail := by
        intro member
        exact absent (by simp [member])
      simp only [List.foldr_cons, if_neg headUnequal, NNRat.zero_add]
      exact induction tailAbsent

private theorem list_sum_indicator
    (values : List α) (target : α)
    (row : α → NNRat) (nodup : values.Nodup)
    (present : target ∈ values) :
    values.foldr (fun value total =>
      (if value = target then row value else 0) + total) 0 = row target := by
  induction values with
  | nil => cases present
  | cons head tail induction =>
      have facts := List.nodup_cons.mp nodup
      by_cases equal : head = target
      · subst head
        have tailZero := list_sum_indicator_absent tail target row facts.1
        simp [List.foldr_cons, tailZero, NNRat.add_zero]
      · have inTail : target ∈ tail :=
          (List.mem_cons.mp present).resolve_left (by
            intro reverse
            exact equal reverse.symm)
        simp only [List.foldr_cons, if_neg equal, NNRat.zero_add]
        exact induction facts.2 inTail

private theorem tableFromList_mass
    (values : List α) (row : α → NNRat)
    (target : α) :
    (tableFromList values row).mass target =
      values.foldr (fun value total =>
        (if value = target then row value else 0) + total) 0 := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      change (FiniteMeasure.scale (row head) (FiniteMeasure.dirac head) +
        tableFromList tail row).mass target =
          (if head = target then row head else 0) +
            tail.foldr (fun value total =>
              (if value = target then row value else 0) + total) 0
      rw [FiniteMeasure.mass_add,
        FiniteMeasure.mass_scale, FiniteMeasure.mass_dirac, induction]
      by_cases equal : head = target
      · subst head
        simp [NNRat.mul_one]
      · simp [equal, NNRat.mul_zero]

private theorem tableFromRows_mass
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat) (input target : α) :
    (tableFromRows enumeration rows input).mass target = rows input target := by
  exact (tableFromList_mass enumeration (rows input) target).trans
    (list_sum_indicator enumeration target (rows input)
      (listed.nodup) (listed.complete target))

omit [DecidableEq α] in
private theorem tableFromList_integral
    (values : List α) (row term : α → NNRat) :
    (tableFromList values row).integral term =
      values.foldr (fun value total => row value * term value + total) 0 := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      change (FiniteMeasure.scale (row head) (FiniteMeasure.dirac head) +
        tableFromList tail row).integral term =
          row head * term head +
            tail.foldr (fun value total => row value * term value + total) 0
      rw [FiniteMeasure.integral_add, FiniteMeasure.integral_scale,
        FiniteMeasure.integral_dirac, induction]

omit [DecidableEq α] in
private theorem tableFromRows_integral
    (enumeration : List α)
    (rows : α → α → NNRat)
    (input : α) (term : α → NNRat) :
    (tableFromRows enumeration rows input).integral term =
      matrixSum enumeration (fun middle => rows input middle * term middle) :=
  tableFromList_integral enumeration (rows input) term

/-- The rational transition matrix after a fixed number of steps. -/
def matrixIterate
    (enumeration : List α)
    (rows : α → α → NNRat) :
    Nat → α → α → NNRat
  | 0, input, output => if input = output then 1 else 0
  | steps + 1, input, output =>
      matrixSum enumeration (fun middle => rows input middle *
        matrixIterate enumeration rows steps middle output)

private def finiteIterate
    (enumeration : List α)
    (rows : α → α → NNRat) :
    Nat → α → FiniteMeasure α
  | 0, input => FiniteMeasure.dirac input
  | steps + 1, input =>
      FiniteMeasure.bind (tableFromRows enumeration rows input)
        (finiteIterate enumeration rows steps)

private theorem finiteIterate_mass
    (enumeration : List α)
    (rows : α → α → NNRat)
    (steps : Nat) (input output : α) :
    (finiteIterate enumeration rows steps input).mass output =
      matrixIterate enumeration rows steps input output := by
  induction steps generalizing input with
  | zero =>
      rw [finiteIterate, matrixIterate, FiniteMeasure.mass_dirac]
  | succ steps induction =>
      rw [finiteIterate, matrixIterate, FiniteMeasure.mass_bind,
        tableFromRows_integral]
      apply congrArg (matrixSum enumeration)
      funext middle
      rw [induction middle]

private theorem toMeasure_singleton_mass
    (table : FiniteMeasure α) (point : α) :
    table.toMeasure (Space.discrete α) (Set.singleton point) =
      (table.mass point).toENNReal := by
  classical
  rw [FiniteMeasure.toMeasure_apply _ table
    (Space.discrete_measurable _), FiniteMeasure.mass_eq_integral_indicator]
  apply congrArg NNRat.toENNReal
  apply FiniteMeasure.integral_congr
  intro value
  simp [Set.singleton]

private theorem tableFromRows_toMeasure
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (input : α) :
    (tableFromRows enumeration rows input).toMeasure (Space.discrete α) =
      kernel input := by
  apply finite_singletons_determine_measure enumeration listed
  intro point
  rw [toMeasure_singleton_mass,
    tableFromRows_mass enumeration listed rows input point]
  exact (represents input point).symm

private theorem finiteIterate_toMeasure
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (steps : Nat) (input : α) :
    (finiteIterate enumeration rows steps input).toMeasure
        (Space.discrete α) =
      (iterate kernel steps input) := by
  induction steps generalizing input with
  | zero =>
      rw [finiteIterate, FiniteMeasure.toMeasure_dirac,
        iterate_zero, Kernel.deterministic_apply]
  | succ steps induction =>
      rw [finiteIterate, FiniteMeasure.toMeasure_bind]
      · rw [tableFromRows_toMeasure enumeration listed rows kernel represents input,
          iterate_succ, Kernel.comp_apply]
      · intro middle
        exact induction middle

private theorem matrixIterate_singleton
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (steps : Nat) (input output : α) :
    (iterate kernel steps input) (Set.singleton output) =
      (matrixIterate enumeration rows steps input output).toENNReal := by
  rw [← finiteIterate_toMeasure enumeration listed rows kernel represents steps input,
    toMeasure_singleton_mass, finiteIterate_mass]

/-- Decide whether one column of a rational matrix power is positive
at every input state. -/
def positiveColumn
    (enumeration : List α)
    (rows : α → α → NNRat) (steps : Nat)
    (output : α) : Bool :=
  enumeration.all fun input =>
    decide (matrixIterate enumeration rows steps input output ≠ 0)

/-- The Boolean check exposes strict positivity at every input state. -/
theorem positiveColumn_iff
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat) (steps : Nat)
    (output : α) :
    positiveColumn enumeration rows steps output = true ↔
      ∀ input, matrixIterate enumeration rows steps input output ≠ 0 := by
  rw [positiveColumn, List.all_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · intro checked input
    exact checked input (listed.complete input)
  · intro checked input _
    exact checked input

private noncomputable def finiteMinimum
    (enumeration : List α)
    (mass : α → ENNReal) : ENNReal :=
  enumeration.foldr (fun input bound => ENNReal.min (mass input) bound)
    ENNReal.one

omit [DecidableEq α] in
private theorem finiteMinimum_le_one
    (enumeration : List α)
    (mass : α → ENNReal) :
    ENNReal.le (finiteMinimum enumeration mass) ENNReal.one := by
  unfold finiteMinimum
  have bound : ∀ values : List α,
      ENNReal.le
        (values.foldr (fun input rest => ENNReal.min (mass input) rest)
          ENNReal.one) ENNReal.one := by
    intro values
    induction values with
    | nil => exact ENNReal.le_refl _
    | cons head tail induction =>
        exact ENNReal.le_trans (ENNReal.min_le_right _ _) induction
  exact bound enumeration

omit [DecidableEq α] in
private theorem finiteMinimum_le
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (mass : α → ENNReal) (input : α) :
    ENNReal.le (finiteMinimum enumeration mass) (mass input) := by
  unfold finiteMinimum
  have onList : ∀ values : List α, input ∈ values →
      ENNReal.le
        (values.foldr (fun state bound => ENNReal.min (mass state) bound)
          ENNReal.one) (mass input) := by
    intro values
    induction values with
    | nil => intro impossible; cases impossible
    | cons head tail induction =>
        intro member
        rcases List.mem_cons.mp member with equal | member
        · subst head
          exact ENNReal.min_le_left _ _
        · exact ENNReal.le_trans (ENNReal.min_le_right _ _)
            (induction member)
  exact onList enumeration (listed.complete input)

omit [DecidableEq α] in
private theorem finiteMinimum_positive
    (enumeration : List α)
    (mass : α → ENNReal)
    (positive : ∀ input, ENNReal.lt ENNReal.zero (mass input)) :
    ENNReal.lt ENNReal.zero (finiteMinimum enumeration mass) := by
  unfold finiteMinimum
  have listed : ∀ values : List α,
      ENNReal.lt ENNReal.zero
        (values.foldr (fun state bound => ENNReal.min (mass state) bound)
          ENNReal.one) := by
    intro values
    induction values with
    | nil =>
        apply ENNReal.zero_lt_iff_ne_zero.mpr
        intro equal
        exact NNReal.one_ne_zero (ENNReal.finite_injective equal)
    | cons head tail induction =>
        simp only [List.foldr_cons]
        rcases ENNReal.le_total (mass head)
            (tail.foldr (fun state bound => ENNReal.min (mass state) bound)
              ENNReal.one) with included | included
        · rw [ENNReal.min_eq_left included]
          exact positive head
        · rw [ENNReal.min_eq_right included]
          exact induction
  exact listed enumeration

/-- The least rational matrix mass in a checked column, capped at one. -/
noncomputable def columnMin
    (enumeration : List α)
    (rows : α → α → NNRat) (steps : Nat)
    (output : α) : ENNReal :=
  finiteMinimum enumeration (fun input =>
    (matrixIterate enumeration rows steps input output).toENNReal)

/-- The least singleton mass of a kernel iterate in one column, capped at one. -/
noncomputable def kernelColumnMin
    (enumeration : List α)
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) (steps : Nat) (output : α) : ENNReal :=
  finiteMinimum enumeration (fun input => (iterate kernel steps input) (Set.singleton output))

private theorem columnMin_eq_kernel
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (steps : Nat) (output : α) :
    columnMin enumeration rows steps output = kernelColumnMin enumeration kernel steps output := by
  unfold columnMin kernelColumnMin
  apply congrArg (finiteMinimum enumeration)
  funext input
  exact (matrixIterate_singleton enumeration listed rows kernel represents steps input output).symm

omit [DecidableEq α] in
/-- A positive singleton column of a finite Markov kernel gives a uniform
Dirac minorization with the least column mass as its weight. -/
theorem positive_column_minorization
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (steps : Nat) (output : α) (stepsPositive : 0 < steps)
    (positive : ∀ input, ENNReal.lt ENNReal.zero
      ((iterate kernel steps input) (Set.singleton output))) :
    ∃ weight : NNReal,
      ENNReal.finite weight = kernelColumnMin enumeration kernel steps output ∧
        Minorization kernel steps weight
          ⟨Measure.dirac (Space.discrete α) output,
            Measure.IsProbability.dirac _ output⟩ := by
  have finite : ENNReal.Finite (kernelColumnMin enumeration kernel steps output) :=
    ENNReal.finite_of_le (finiteMinimum_le_one enumeration _) True.intro
  rcases ENNReal.exists_finite_of_finite finite with ⟨weight, weightEqual⟩
  refine ⟨weight, weightEqual.symm, ?_⟩
  have weightPositive : NNReal.lt NNReal.zero weight := by
    have strict := finiteMinimum_positive enumeration _ positive
    rw [← kernelColumnMin, weightEqual] at strict
    exact strict
  have weightAtMostOne : NNReal.le weight NNReal.one := by
    have included := finiteMinimum_le_one enumeration
      (fun input => (iterate kernel steps input) (Set.singleton output))
    change ENNReal.le (kernelColumnMin enumeration kernel steps output) ENNReal.one
      at included
    rw [weightEqual] at included
    exact included
  refine {
    markov := markov
    stepsPositive := stepsPositive
    weightPositive := weightPositive
    weightAtMostOne := weightAtMostOne
    lower := ?_
  }
  intro input event measurable
  rw [Measure.smul_apply_measurable _ _ measurable]
  change ENNReal.le
    (ENNReal.mul (ENNReal.finite weight)
      ((Measure.dirac _ output) event))
    ((iterate kernel steps input) event)
  by_cases member : event output
  · rw [Measure.dirac_apply_of_mem _ output measurable member,
      ENNReal.mul_one]
    have singletonIncluded : Set.Subset (Set.singleton output) event := by
      intro value equal
      subst value
      exact member
    have massIncluded := (iterate kernel steps input).mono singletonIncluded
    have columnIncluded := finiteMinimum_le enumeration listed
      (fun state => (iterate kernel steps state) (Set.singleton output)) input
    change ENNReal.le (kernelColumnMin enumeration kernel steps output)
      ((iterate kernel steps input) (Set.singleton output)) at columnIncluded
    rw [weightEqual] at columnIncluded
    exact ENNReal.le_trans columnIncluded massIncluded
  · rw [Measure.dirac_apply_of_not_mem _ output measurable member,
      ENNReal.mul_zero]
    exact ENNReal.zero_le _

/-- Every state can reach every other state with positive probability at
some finite time. -/
def Irreducible
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) : Prop :=
  ∀ input output, ∃ steps : Nat,
    ENNReal.lt ENNReal.zero
      ((iterate kernel steps input) (Set.singleton output))

/-- The state `output` is reached from `input` with positive probability at
some finite time. -/
def Reaches
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) (input output : α) : Prop :=
  ∃ steps : Nat,
    ENNReal.lt ENNReal.zero
      ((iterate kernel steps input) (Set.singleton output))

/-- At one state, the greatest common divisor of the positive return times is
one. -/
def AperiodicAt
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) (point : α) : Prop :=
  ∀ divisor : Nat,
    (∀ steps, ENNReal.lt ENNReal.zero
      ((iterate kernel steps point) (Set.singleton point)) →
      divisor ∣ steps) → divisor = 1

/-- The greatest common divisor of the positive return times is one. -/
def Aperiodic
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) : Prop :=
  ∀ input : α, AperiodicAt kernel input

private theorem positive_path_comp
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (input middle output : α) (first second : Nat)
    (firstPositive : ENNReal.lt ENNReal.zero
      ((iterate kernel first input) (Set.singleton middle)))
    (secondPositive : ENNReal.lt ENNReal.zero
      ((iterate kernel second middle) (Set.singleton output))) :
    ENNReal.lt ENNReal.zero
      ((iterate kernel (first + second) input) (Set.singleton output)) := by
  let function := fun state =>
    (iterate kernel second state) (Set.singleton output)
  have singleMeasurable :
      (Space.discrete α).Measurable (Set.singleton middle) :=
    Space.discrete_measurable _
  have indicatorLe : ∀ state,
      ENNReal.le
        (ennrealIndicator (Set.singleton middle) (fun _ => function middle) state)
        (function state) := by
    intro state
    by_cases equal : state = middle
    · subst state
      simp [ennrealIndicator, ennrealPiecewise, Set.singleton,
        ENNReal.le_refl]
    · simp [ennrealIndicator, ennrealPiecewise, Set.singleton,
        equal, ENNReal.zero_le]
  have lower := lintegral_mono (iterate kernel first input) indicatorLe
  rw [lintegral_indicator _ (Set.singleton middle) singleMeasurable,
    lintegral_const, Measure.restrict_apply_univ,
    ENNReal.mul_comm] at lower
  have productPositive : ENNReal.lt ENNReal.zero
      (ENNReal.mul
        ((iterate kernel first input) (Set.singleton middle))
        ((iterate kernel second middle) (Set.singleton output))) := by
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro zero
    rcases ENNReal.mul_eq_zero_iff.mp zero with firstZero | secondZero
    · rw [firstZero] at firstPositive
      exact firstPositive.right (ENNReal.le_refl _)
    · rw [secondZero] at secondPositive
      exact secondPositive.right (ENNReal.le_refl _)
  rw [iterate_add,
    comp_apply_measurable _ _ input (Space.discrete_measurable _)]
  exact ⟨ENNReal.le_trans productPositive.left lower,
    fun reverse => productPositive.right
      (ENNReal.le_trans lower reverse)⟩

omit [DecidableEq α] in
private theorem probability_positive_singleton
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (measure : Measure (Space.discrete α))
    (probability : Measure.IsProbability measure) :
    ∃ point : α,
      ENNReal.lt ENNReal.zero (measure (Set.singleton point)) := by
  classical
  by_cases present : ∃ point : α,
      ENNReal.lt ENNReal.zero (measure (Set.singleton point))
  · exact present
  have zeroMass (point : α) :
      measure (Set.singleton point) = ENNReal.zero := by
    by_cases zero : measure (Set.singleton point) = ENNReal.zero
    · exact zero
    · exact False.elim (present
        ⟨point, ENNReal.zero_lt_iff_ne_zero.mpr zero⟩)
  have equal : measure = Measure.zero (Space.discrete α) := by
    apply finite_singletons_determine_measure enumeration listed
    intro point
    rw [zeroMass, Measure.zero_apply]
  have total := probability.univ_eq_one
  rw [equal, Measure.zero_apply] at total
  exact False.elim (ENNReal.one_ne_zero total.symm)

/-- One step of positive probability followed by a reach is a reach. -/
theorem reaches_step
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    {input middle output : α}
    (first : ENNReal.lt ENNReal.zero (kernel input (Set.singleton middle)))
    (rest : Reaches kernel middle output) :
    Reaches kernel input output := by
  rcases rest with ⟨later, secondPositive⟩
  have onePositive : ENNReal.lt ENNReal.zero
      ((iterate kernel 1 input) (Set.singleton middle)) := by
    rw [iterate_succ, iterate_zero, Kernel.comp_apply,
      Measure.bind_deterministic, Measure.map_id]
    exact first
  exact ⟨1 + later,
    positive_path_comp kernel input middle output 1 later onePositive secondPositive⟩

omit [DecidableEq α] in
/-- A state reaches itself. -/
theorem reaches_refl
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) (point : α) :
    Reaches kernel point point := by
  refine ⟨0, ?_⟩
  rw [iterate_zero, Kernel.deterministic_apply, Measure.dirac_apply_of_mem]
  · exact ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero
  · exact Space.discrete_measurable _
  · rfl

omit [DecidableEq α] in
/-- A state that holds with positive probability is aperiodic: one is a
return time. -/
theorem aperiodicAt_of_hold
    (kernel : Kernel (Space.discrete α) (Space.discrete α)) {point : α}
    (hold : ENNReal.lt ENNReal.zero (kernel point (Set.singleton point))) :
    AperiodicAt kernel point := by
  intro divisor divides
  have once : ENNReal.lt ENNReal.zero
      ((iterate kernel 1 point) (Set.singleton point)) := by
    rw [iterate_succ, iterate_zero, Kernel.comp_apply,
      Measure.bind_deterministic, Measure.map_id]
    exact hold
  exact Nat.dvd_one.mp (divides 1 once)

private theorem positive_return
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (point : α) (accessible : ∀ input, Reaches kernel input point) :
    ∃ steps : Nat, 0 < steps ∧
      ENNReal.lt ENNReal.zero
        ((iterate kernel steps point) (Set.singleton point)) := by
  rcases probability_positive_singleton enumeration listed (kernel point) (markov point) with
    ⟨middle, firstPositive⟩
  rcases accessible middle with ⟨later, secondPositive⟩
  have onePositive : ENNReal.lt ENNReal.zero
      ((iterate kernel 1 point) (Set.singleton middle)) := by
    rw [iterate_succ, iterate_zero, Kernel.comp_apply,
      Measure.bind_deterministic, Measure.map_id]
    exact firstPositive
  have positiveSteps : 0 < 1 + later := by
    simpa only [Nat.add_comm] using Nat.zero_lt_succ later
  exact ⟨1 + later, positiveSteps,
    positive_path_comp kernel point middle point 1 later
      onePositive secondPositive⟩

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

private def residueReachable (members : Nat → Prop) (period residue : Nat) :
    Prop :=
  ∃ value, members value ∧ value % period = residue

private theorem residue_zero (members : Nat → Prop)
    (zero : members 0) (period : Nat) :
    residueReachable members period 0 := by
  exact ⟨0, zero, Nat.zero_mod _⟩

private theorem residue_add (members : Nat → Prop) (period : Nat)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {first second : Nat}
    (left : residueReachable members period first)
    (right : residueReachable members period second) :
    residueReachable members period ((first + second) % period) := by
  rcases left with ⟨left, leftPresent, leftMod⟩
  rcases right with ⟨right, rightPresent, rightMod⟩
  refine ⟨left + right, add left right leftPresent rightPresent, ?_⟩
  rw [Nat.add_mod, leftMod, rightMod]

private theorem residue_inverse (members : Nat → Prop) (period : Nat)
    (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    {residue : Nat} (present : residueReachable members period residue) :
    ∃ inverse, residueReachable members period inverse ∧
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
    (left : residueReachable members period first)
    (right : residueReachable members period second)
    (firstSmall : first < period) (included : second ≤ first) :
    residueReachable members period (first - second) := by
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
      residueReachable members period residue) :
    ∃ least, 0 < least ∧ residueReachable members period least ∧
      ∀ residue, 0 < residue → residue < least →
        ¬residueReachable members period residue := by
  rcases existsPositive with ⟨candidate, positive, reachable⟩
  have descend : ∀ bound : Nat, 0 < bound →
      residueReachable members period bound →
      ∃ least, 0 < least ∧ residueReachable members period least ∧
        ∀ residue, 0 < residue → residue < least →
          ¬residueReachable members period residue := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound smaller =>
        intro boundPositive boundReachable
        by_cases existsSmaller : ∃ residue, 0 < residue ∧
            residue < bound ∧ residueReachable members period residue
        · rcases existsSmaller with
            ⟨residue, residuePositive, residueLess, residueReachable⟩
          exact smaller residue residueLess residuePositive residueReachable
        · refine ⟨bound, boundPositive, boundReachable, ?_⟩
          intro residue residuePositive residueLess residueReachable
          exact existsSmaller
            ⟨residue, residuePositive, residueLess, residueReachable⟩
  exact descend candidate positive reachable

private theorem residue_min_dvd (members : Nat → Prop) (period : Nat)
    (periodPositive : 0 < period) (zero : members 0)
    (add : ∀ left right, members left → members right →
      members (left + right))
    (least : Nat) (leastPositive : 0 < least)
    (leastReachable : residueReachable members period least)
    (minimal : ∀ residue, 0 < residue → residue < least →
      ¬residueReachable members period residue) :
    ∀ residue, residueReachable members period residue →
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
    (leastReachable : residueReachable members period least)
    (minimal : ∀ residue, 0 < residue → residue < least →
      ¬residueReachable members period residue) : least ∣ period := by
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
    residueReachable members period (1 % period) := by
  by_cases positive : ∃ residue, 0 < residue ∧
      residueReachable members period residue
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

private theorem semigroup_eventually (members : Nat → Prop)
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

omit [DecidableEq α] in
private theorem list_entry_le  (values : List α)
    (entry : α → Nat) (input : α) (present : input ∈ values) :
    entry input ≤ values.foldr (fun point bound => max (entry point) bound) 0 := by
  induction values with
  | nil => cases present
  | cons head tail induction =>
      rcases List.mem_cons.mp present with equal | inTail
      · subst input
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction inTail) (Nat.le_max_right _ _)

/-- On a finite state space, a state that every state reaches and that is
aperiodic gives a positive column in one power, hence a uniform minorization
toward that state. The chain need not be irreducible: states the target never
returns to are allowed. -/
theorem finite_accessible_aperiodic_minorization
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (target : α)
    (accessible : ∀ input, Reaches kernel input target)
    (aperiodic : AperiodicAt kernel target) :
    ∃ steps : Nat, ∃ weight : NNReal,
      ∃ reference : Giry.Law (Space.discrete α),
        Minorization kernel steps weight reference := by
  classical
  let returns : Nat → Prop := fun steps =>
    ENNReal.lt ENNReal.zero
      ((iterate kernel steps target) (Set.singleton target))
  have returnZero : returns 0 := by
    change ENNReal.lt ENNReal.zero
      ((iterate kernel 0 target) (Set.singleton target))
    rw [iterate_zero, Kernel.deterministic_apply,
      Measure.dirac_apply_of_mem]
    · exact ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero
    · exact Space.discrete_measurable _
    · rfl
  have returnAdd (first second : Nat)
      (firstPositive : returns first) (secondPositive : returns second) :
      returns (first + second) :=
    positive_path_comp kernel target target target first second
      firstPositive secondPositive
  rcases positive_return enumeration listed kernel markov target accessible with
    ⟨period, periodPositive, periodPresent⟩
  rcases semigroup_eventually returns period periodPositive periodPresent
      returnZero returnAdd aperiodic with
    ⟨threshold, laterReturns⟩
  let entry : α → Nat := fun input =>
    (accessible input).choose
  have entryPositive (input : α) : ENNReal.lt ENNReal.zero
      ((iterate kernel (entry input) input) (Set.singleton target)) :=
    (accessible input).choose_spec
  let bound := enumeration.foldr
    (fun point current => max (entry point) current) 0
  have entryBound (input : α) : entry input ≤ bound :=
    list_entry_le enumeration entry input
      (listed.complete input)
  let steps := max (threshold + bound) 1
  have stepsPositive : 0 < steps := by
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_max_right _ _)
  have columnPositive (input : α) : ENNReal.lt ENNReal.zero
      ((iterate kernel steps input) (Set.singleton target)) := by
    let remaining := steps - entry input
    have enough : threshold ≤ remaining := by
      have large : threshold + bound ≤ steps := Nat.le_max_left _ _
      have small := entryBound input
      dsimp [remaining]
      omega
    have split : steps = entry input + remaining := by
      have large : threshold + bound ≤ steps := Nat.le_max_left _ _
      have small := entryBound input
      dsimp [remaining]
      omega
    rw [split]
    exact positive_path_comp kernel input target target (entry input)
      remaining (entryPositive input) (laterReturns remaining enough)
  rcases positive_column_minorization enumeration listed kernel markov steps target
      stepsPositive columnPositive with ⟨weight, _, certificate⟩
  exact ⟨steps, weight,
    ⟨Measure.dirac _ target, Measure.IsProbability.dirac _ target⟩,
    certificate⟩

/-- On a nonempty finite state space, irreducibility and aperiodicity give a
positive column in one power, hence a uniform minorization. -/
theorem finite_irreducible_aperiodic_minorization
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (nonempty : Nonempty (α))
    (irreducible : Irreducible kernel)
    (aperiodic : Aperiodic kernel) :
    ∃ steps : Nat, ∃ weight : NNReal,
      ∃ reference : Giry.Law (Space.discrete α),
        Minorization kernel steps weight reference :=
  finite_accessible_aperiodic_minorization enumeration listed kernel markov
    (Classical.choice nonempty) (fun input => irreducible input _) (aperiodic _)

/-- A positive column of a rational matrix power supplies a uniform
minorization of the represented Markov kernel. The weight is the minimum of
the column, and the reference law is Dirac at that column. -/
theorem positiveColumn_sound_exact
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (steps : Nat) (output : α) (stepsPositive : 0 < steps)
    (checked : positiveColumn enumeration rows steps output = true) :
    ∃ weight : NNReal,
      ENNReal.finite weight = columnMin enumeration rows steps output ∧
        Minorization kernel steps weight
          ⟨Measure.dirac (Space.discrete α) output,
            Measure.IsProbability.dirac _ output⟩ := by
  have positive (input : α) : ENNReal.lt ENNReal.zero
      ((iterate kernel steps input) (Set.singleton output)) := by
    rw [matrixIterate_singleton enumeration listed rows kernel represents steps input output]
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro equal
    exact ((positiveColumn_iff enumeration listed rows steps output).mp checked input)
      ((NNRat.toENNReal_eq_zero_iff _).mp equal)
  rcases positive_column_minorization enumeration listed kernel markov steps output
      stepsPositive positive with ⟨weight, equal, certificate⟩
  exact ⟨weight, equal.trans
    (columnMin_eq_kernel enumeration listed rows kernel represents steps output).symm,
    certificate⟩

/-- A successful rational column check yields the named minorization premise
for the represented Markov kernel. -/
theorem positiveColumn_sound
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (rows : α → α → NNRat)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (represents : ∀ input output,
      (kernel input) (Set.singleton output) =
        (rows input output).toENNReal)
    (steps : Nat) (output : α) (stepsPositive : 0 < steps)
    (checked : positiveColumn enumeration rows steps output = true) :
    ∃ weight : NNReal,
      ∃ reference : Giry.Law (Space.discrete α),
        Minorization kernel steps weight reference := by
  rcases positiveColumn_sound_exact enumeration listed rows kernel markov represents steps output
      stepsPositive checked with ⟨weight, _, certificate⟩
  let reference : Giry.Law (Space.discrete α) :=
    ⟨Measure.dirac _ output, Measure.IsProbability.dirac _ output⟩
  exact ⟨weight, reference, certificate⟩

namespace TwoState

private def enumeration : List (Fin 2) := List.finRange 2

private theorem listed : FiniteEnumeration enumeration :=
  FiniteEnumeration.finRange 2

private def halfRational : NNRat := FiniteExample.half

/-- The nonnegative real value of the rational half used in the two-state rate. -/
def halfWeight : NNReal :=
  NNReal.ofRat halfRational.val halfRational.nonnegative

/-- Both states transition to the fair law. -/
def rows : Fin 2 → Fin 2 → NNRat :=
  fun _ _ => halfRational

private theorem rows_total (input : Fin 2) :
    (tableFromRows enumeration rows input).total = 1 := by
  rw [tableFromRows_total enumeration]
  change halfRational + (halfRational + 0) = 1
  rw [NNRat.add_zero]
  exact FiniteExample.half_add_half

private theorem matrix_one (input output : Fin 2) :
    matrixIterate enumeration rows 1 input output = halfRational := by
  calc
    matrixIterate enumeration rows 1 input output =
        matrixSum enumeration (fun middle =>
          if middle = output then rows input middle else 0) := by
      change matrixSum enumeration (fun middle =>
        rows input middle * (if middle = output then 1 else 0)) = _
      apply congrArg (matrixSum enumeration)
      funext middle
      by_cases equal : middle = output
      · simp [equal, NNRat.mul_one]
      · simp [equal, NNRat.mul_zero]
    _ = rows input output :=
      list_sum_indicator enumeration output (rows input)
        listed.nodup (listed.complete output)
    _ = halfRational := rfl

private theorem halfWeight_embedding :
    ENNReal.finite halfWeight = halfRational.toENNReal := rfl

private theorem half_add_half :
    ENNReal.add halfRational.toENNReal halfRational.toENNReal =
      ENNReal.one := by
  rw [← NNRat.toENNReal_add]
  change (FiniteExample.half + FiniteExample.half).toENNReal = ENNReal.one
  rw [FiniteExample.half_add_half, NNRat.toENNReal_one]

private theorem half_le_one :
    ENNReal.le halfRational.toENNReal ENNReal.one := by
  rw [← half_add_half]
  have included := ENNReal.add_le_add_left
    (ENNReal.zero_le halfRational.toENNReal) halfRational.toENNReal
  rwa [ENNReal.add_zero] at included

private theorem columnMin_half (output : Fin 2) :
    columnMin enumeration rows 1 output = ENNReal.finite halfWeight := by
  change ENNReal.min (matrixIterate enumeration rows 1 ⟨0, by decide⟩ output).toENNReal
    (ENNReal.min (matrixIterate enumeration rows 1 ⟨1, by decide⟩ output).toENNReal
      ENNReal.one) = ENNReal.finite halfWeight
  rw [matrix_one, matrix_one, ENNReal.min_eq_left half_le_one,
    ENNReal.min_eq_left (ENNReal.le_refl _), halfWeight_embedding]

/-- The fair two-state law interpreted from rational rows. -/
noncomputable def law : Giry.Law (Space.discrete (Fin 2)) :=
  ⟨(tableFromRows enumeration rows ⟨0, by decide⟩).toMeasure _,
    FiniteMeasure.toMeasure_isProbability _ _
      (rows_total ⟨0, by decide⟩)⟩

/-- A constant two-state Markov kernel with a nonzero value in each column. -/
noncomputable def kernel : Kernel (Space.discrete (Fin 2))
    (Space.discrete (Fin 2)) :=
  Kernel.const _ law.val

private theorem rows_same (input : Fin 2) :
    tableFromRows enumeration rows input = tableFromRows enumeration rows ⟨0, by decide⟩ := by
  rfl

private theorem represents (input output : Fin 2) :
    (kernel input) (Set.singleton output) =
      (rows input output).toENNReal := by
  rw [kernel, Kernel.const_apply]
  change (tableFromRows enumeration rows ⟨0, by decide⟩).toMeasure _
    (Set.singleton output) = _
  rw [← rows_same input, toMeasure_singleton_mass,
    tableFromRows_mass enumeration listed]

private theorem markov (input : Fin 2) :
    Measure.IsProbability (kernel input) := by
  rw [kernel, Kernel.const_apply]
  exact law.property

/-- The rational checker accepts the first column after one step. -/
theorem positive_column :
    positiveColumn enumeration rows 1 ⟨0, by decide⟩ = true := by
  apply (positiveColumn_iff enumeration listed rows 1 ⟨0, by decide⟩).mpr
  intro input
  rw [matrix_one]
  exact FiniteExample.half_ne_zero

/-- The checker supplies a minorization for the two-state kernel. -/
theorem checked_minorization :
    ∃ weight : NNReal,
      ∃ reference : Giry.Law (Space.discrete (Fin 2)),
        Minorization kernel 1 weight reference :=
  positiveColumn_sound enumeration listed rows kernel markov represents 1
    ⟨0, by decide⟩ (by decide) positive_column

private theorem exact_minorization :
    ∃ reference : Giry.Law (Space.discrete (Fin 2)),
      Minorization kernel 1 halfWeight reference := by
  rcases positiveColumn_sound_exact enumeration listed rows kernel markov represents 1
      ⟨0, by decide⟩ (by decide) positive_column with
    ⟨weight, weightMin, certificate⟩
  have equal : weight = halfWeight :=
    ENNReal.finite_injective
      (weightMin.trans (columnMin_half ⟨0, by decide⟩))
  subst weight
  let reference : Giry.Law (Space.discrete (Fin 2)) :=
    ⟨Measure.dirac _ (⟨0, by decide⟩ : Fin 2),
      Measure.IsProbability.dirac _ (⟨0, by decide⟩ : Fin 2)⟩
  exact ⟨reference, certificate⟩

private theorem invariant : law.val.bind kernel = law.val := by
  rw [kernel, Measure.bind_const, law.property.univ_eq_one,
    Measure.one_smul]

private theorem half_sub :
    ENNReal.sub ENNReal.one (ENNReal.finite halfWeight) =
      ENNReal.finite halfWeight := by
  rw [halfWeight_embedding, ← half_add_half]
  exact ENNReal.add_sub_cancel_right True.intro

/-- Every probability start reaches the fair law with the explicit geometric
bound `(1/2)^n` on total variation. -/
theorem explicit_rate (start : Giry.Law (Space.discrete (Fin 2)))
    (count : Nat) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨start.val.bind (iterate kernel count),
          start.property.bind (iterate kernel count)
            (iterate_isProbability kernel markov count)⟩ law)
      (ENNReal.mul (ENNReal.pow (ENNReal.finite halfWeight) count)
        (Giry.Law.totalVariation start law)) := by
  rcases exact_minorization with ⟨reference, certificate⟩
  have bound := minorization_contraction certificate law start invariant count
  simpa only [Nat.div_one, half_sub] using bound

end TwoState

end Problib.Measure.Kernel
