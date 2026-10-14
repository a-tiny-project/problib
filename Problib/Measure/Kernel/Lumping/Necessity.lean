module
public import Problib.Measure.Kernel.Lumping
public import Problib.Measure.Kernel.Piecewise
public import Problib.Measure.Configuration.Unordered
public import Problib.Measure.Configuration.Power
import Problib.Measure.Measurability

set_option autoImplicit false
namespace Problib.Measure
open Problib.Real Measure
public section
attribute [local instance] Classical.propDecidable

/-- A fair draw on the discrete Bool space. -/
@[expose] public noncomputable def fairBool : Measure (Space.discrete Bool) :=
  Measure.add
    (Measure.smul (ENNReal.half ENNReal.one) (Measure.dirac _ false))
    (Measure.smul (ENNReal.half ENNReal.one) (Measure.dirac _ true))

public theorem fairBool_probability : Measure.IsProbability fairBool := by
  constructor
  rw [fairBool, Measure.add_apply_measurable _ _ (Space.discrete Bool).univ,
    Measure.smul_apply_measurable _ _ (Space.discrete Bool).univ,
    Measure.smul_apply_measurable _ _ (Space.discrete Bool).univ,
    Measure.dirac_apply_univ, Measure.dirac_apply_univ,
    ENNReal.mul_one, ENNReal.half_add_half]

public theorem fairBool_false_mass :
    fairBool (Set.singleton false) = ENNReal.half ENNReal.one := by
  rw [fairBool, Measure.add_apply_measurable _ _ (show
    (Space.discrete Bool).Measurable (Set.singleton false) from trivial),
    Measure.smul_apply_measurable _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton false) from trivial),
    Measure.smul_apply_measurable _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton false) from trivial),
    Measure.dirac_apply _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton false) from trivial),
    Measure.dirac_apply _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton false) from trivial)]
  simp [Set.singleton, ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero]

public theorem fairBool_true_mass :
    fairBool (Set.singleton true) = ENNReal.half ENNReal.one := by
  rw [fairBool, Measure.add_apply_measurable _ _ (show
    (Space.discrete Bool).Measurable (Set.singleton true) from trivial),
    Measure.smul_apply_measurable _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton true) from trivial),
    Measure.smul_apply_measurable _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton true) from trivial),
    Measure.dirac_apply _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton true) from trivial),
    Measure.dirac_apply _ _ (show
      (Space.discrete Bool).Measurable (Set.singleton true) from trivial)]
  simp [Set.singleton, ENNReal.mul_zero, ENNReal.mul_one, ENNReal.zero_add]

public theorem empty_list_measurable :
    (Space.list (Space.discrete Bool)).Measurable
      (fun values => values = []) := by
  have measured := ListSpace.length_measurable (Space.discrete Bool)
    (set := fun length => length = 0) trivial
  have equal : Set.preimage List.length (fun length => length = 0) =
      (fun values : List Bool => values = []) := by
    funext values
    cases values <;> simp [Set.preimage]
  rw [equal] at measured
  exact measured

public theorem prepend_measurable (bit : Bool) :
    MeasurableMap (Space.list (Space.discrete Bool))
      (Space.list (Space.discrete Bool)) (fun values => bit :: values.tail) := by
  measurability [ListSpace.cons_measurable (Space.discrete Bool),
    ListSpace.tail_measurable (Space.discrete Bool)]

public noncomputable def resampleEmpty :
    Kernel (Space.list (Space.discrete Bool))
      (Space.list (Space.discrete Bool)) :=
  Kernel.deterministic (fun _ => ([] : List Bool))
    (MeasurableMap.constant _ _ [])

public noncomputable def resampleNonempty :
    Kernel (Space.list (Space.discrete Bool))
      (Space.list (Space.discrete Bool)) :=
  Kernel.add
    (Kernel.smul (ENNReal.half ENNReal.one)
      (Kernel.deterministic (fun values => false :: values.tail)
        (prepend_measurable false)))
    (Kernel.smul (ENNReal.half ENNReal.one)
      (Kernel.deterministic (fun values => true :: values.tail)
        (prepend_measurable true)))

/-- Resample the first coordinate while fixing the tail. The empty list
remains empty. -/
@[expose] public noncomputable def resampleFirst :
    Kernel (Space.list (Space.discrete Bool))
      (Space.list (Space.discrete Bool)) :=
  Kernel.piecewise (fun values => values = []) empty_list_measurable
    resampleEmpty resampleNonempty

public theorem resampleFirst_markov (values : List Bool) :
    Measure.IsProbability (resampleFirst values) := by
  constructor
  by_cases empty : values = []
  · rw [resampleFirst,
      Kernel.piecewise_apply_of_mem (fun v : List Bool => v = [])
        empty_list_measurable resampleEmpty resampleNonempty values empty]
    change (Measure.dirac (Space.list (Space.discrete Bool)) []) Set.univ = ENNReal.one
    exact Measure.dirac_apply_univ _ _
  · rw [resampleFirst,
      Kernel.piecewise_apply_of_not_mem (fun v : List Bool => v = [])
        empty_list_measurable resampleEmpty resampleNonempty values empty,
      resampleNonempty,
      Kernel.add_apply, Kernel.smul_apply, Kernel.smul_apply,
      Kernel.deterministic_apply, Kernel.deterministic_apply,
      Measure.add_apply_measurable _ _ (Space.list (Space.discrete Bool)).univ,
      Measure.smul_apply_measurable _ _ (Space.list (Space.discrete Bool)).univ,
      Measure.smul_apply_measurable _ _ (Space.list (Space.discrete Bool)).univ,
      Measure.dirac_apply_univ, Measure.dirac_apply_univ,
      ENNReal.mul_one, ENNReal.half_add_half]

public theorem resampleFirst_cons (head : Bool) (tail : List Bool) :
    resampleFirst (head :: tail) =
      Measure.add
        (Measure.smul (ENNReal.half ENNReal.one)
          (Measure.dirac (Space.list (Space.discrete Bool)) (false :: tail)))
        (Measure.smul (ENNReal.half ENNReal.one)
          (Measure.dirac (Space.list (Space.discrete Bool)) (true :: tail))) := by
  rw [resampleFirst,
    Kernel.piecewise_apply_of_not_mem (fun v : List Bool => v = [])
      empty_list_measurable resampleEmpty resampleNonempty
      (head :: tail) (by nofun)]
  rfl

private theorem cons_bit_measurable (bit : Bool) :
    MeasurableMap (Space.list (Space.discrete Bool))
      (Space.list (Space.discrete Bool)) (fun values => bit :: values) := by
  measurability [ListSpace.cons_measurable (Space.discrete Bool)]

private theorem fairBool_lintegral (integrand : Bool → ENNReal) :
    lintegral fairBool integrand =
      ENNReal.add (ENNReal.mul (ENNReal.half ENNReal.one) (integrand false))
        (ENNReal.mul (ENNReal.half ENNReal.one) (integrand true)) := by
  rw [fairBool, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac _ _ (fun _ => trivial),
    lintegral_dirac _ _ (fun _ => trivial)]

private theorem lintegral_dirac_cons
    (law : Measure (Space.list (Space.discrete Bool))) (bit : Bool)
    {set : Set (List Bool)}
    (setMeasurable : (Space.list (Space.discrete Bool)).Measurable set) :
    lintegral law (fun values =>
      Measure.dirac (Space.list (Space.discrete Bool)) (bit :: values) set) =
      law (Set.preimage (fun values => bit :: values) set) := by
  rw [Measure.apply_eq_lintegral_indicator law
    (cons_bit_measurable bit setMeasurable)]
  apply lintegral_congr
  intro values
  rw [Measure.dirac_apply _ _ setMeasurable]
  rfl

/-- Resampling the first coordinate from the fair law preserves every iid
fair Bool power, so the kernel that fails to lump is a valid move. -/
public theorem resampleFirst_invariant_iid (finite : Measure.SFinite fairBool)
    (count : Nat) :
    (Measure.listPower fairBool finite count).bind resampleFirst =
      Measure.listPower fairBool finite count := by
  cases count with
  | zero =>
      rw [Measure.listPower_zero, Measure.dirac_bind, resampleFirst,
        Kernel.piecewise_apply_of_mem (fun v : List Bool => v = [])
          empty_list_measurable resampleEmpty resampleNonempty [] rfl]
      rfl
  | succ count =>
      rw [Measure.listPower_succ, Measure.bind_map]
      apply Measure.ext
      intro set setMeasurable
      have kernelMeasurable := (resampleFirst.precomp
        (fun input : Bool × List Bool => input.1 :: input.2)
        (ListSpace.cons_measurable (Space.discrete Bool))).measurable setMeasurable
      have diracMeasurable : ∀ bit : Bool, ENNRealMeasurable
          (Space.list (Space.discrete Bool))
          (fun values => Measure.dirac (Space.list (Space.discrete Bool))
            (bit :: values) set) := fun bit =>
        (Kernel.deterministic (fun values => bit :: values)
          (cons_bit_measurable bit)).measurable setMeasurable
      have inner : ∀ head : Bool,
          lintegral (Measure.listPower fairBool finite count) (fun values =>
            resampleFirst.precomp
              (fun input : Bool × List Bool => input.1 :: input.2)
              (ListSpace.cons_measurable (Space.discrete Bool))
              (head, values) set) =
          ENNReal.add
            (ENNReal.mul (ENNReal.half ENNReal.one)
              (Measure.listPower fairBool finite count
                (Set.preimage (fun values => false :: values) set)))
            (ENNReal.mul (ENNReal.half ENNReal.one)
              (Measure.listPower fairBool finite count
                (Set.preimage (fun values => true :: values) set))) := by
        intro head
        rw [← lintegral_dirac_cons _ false setMeasurable,
          ← lintegral_dirac_cons _ true setMeasurable,
          ← lintegral_smul _ _ (diracMeasurable false),
          ← lintegral_smul _ _ (diracMeasurable true),
          ← lintegral_add _
            (ENNRealMeasurable.const_mul _ (diracMeasurable false))
            (ENNRealMeasurable.const_mul _ (diracMeasurable true))]
        apply lintegral_congr
        intro values
        rw [Kernel.precomp_apply, resampleFirst_cons,
          Measure.add_apply_measurable _ _ setMeasurable,
          Measure.smul_apply_measurable _ _ setMeasurable,
          Measure.smul_apply_measurable _ _ setMeasurable]
      rw [Measure.bind_apply _ _ setMeasurable, Measure.map_apply _ _ _ setMeasurable,
        lintegral_prod _ _ _ kernelMeasurable, lintegral_congr fairBool inner,
        lintegral_const, fairBool_probability.univ_eq_one, ENNReal.mul_one,
        Measure.prod_apply _ _ _
          (ListSpace.cons_measurable (Space.discrete Bool) setMeasurable),
        fairBool_lintegral]
      rfl

private theorem bool_list_singleton_measurable (values : List Bool) :
    (Space.list (Space.discrete Bool)).Measurable
      (fun other => other = values) := by
  induction values with
  | nil => exact empty_list_measurable
  | cons head tail induction =>
      have selected :
          (Space.sum (Space.discrete Unit)
            (Space.product (Space.discrete Bool)
              (Space.list (Space.discrete Bool)))).Measurable
            (fun choice => match choice with
              | .inl _ => False
              | .inr (value, rest) => value = head ∧ rest = tail) := by
        constructor
        · exact (Space.discrete Unit).empty
        · have measured := Space.product_set_measurable
            (Space.discrete Bool) (Space.list (Space.discrete Bool))
            (leftSet := fun value => value = head) trivial induction
          have equal : Set.product (fun value : Bool => value = head)
              (fun rest : List Bool => rest = tail) =
              Set.preimage Sum.inr (fun choice : Sum Unit (Bool × List Bool) =>
                match choice with
                | .inl _ => False
                | .inr (value, rest) => value = head ∧ rest = tail) := by
            funext input
            cases input
            rfl
          rw [equal] at measured
          exact measured
      have measured := ListSpace.view_measurable (Space.discrete Bool) selected
      have equal : Set.preimage ListSpace.view
          (fun choice : Sum Unit (Bool × List Bool) =>
            match choice with
            | .inl _ => False
            | .inr (value, rest) => value = head ∧ rest = tail) =
          (fun other : List Bool => other = head :: tail) := by
        funext other
        cases other with
        | nil => simp [Set.preimage, ListSpace.view]
        | cons value rest => simp [Set.preimage, ListSpace.view]
      rw [equal] at measured
      exact measured

private theorem unorder_all_true_singleton_measurable :
    (Space.unordered (Space.discrete Bool)).Measurable
      (Set.singleton (unorder [true, true])) := by
  have measured := bool_list_singleton_measurable [true, true]
  have equal :
      Set.preimage unorder (Set.singleton (unorder [true, true])) =
        (fun values : List Bool => values = [true, true]) := by
    funext values
    apply propext
    constructor
    · intro member
      have permutation : values.Perm [true, true] := Quotient.exact member
      have repeated : values.Perm (List.replicate 2 true) := permutation
      exact List.perm_replicate.mp repeated
    · intro equal
      subst values
      rfl
  rw [← equal] at measured
  exact measured

private theorem unorder_with_false_ne_all_true (first second : Bool)
    (containsFalse : first = false ∨ second = false) :
    unorder [first, second] ≠ unorder [true, true] := by
  intro equal
  have permutation : [first, second].Perm [true, true] := Quotient.exact equal
  have repeated : [first, second].Perm (List.replicate 2 true) := permutation
  have same := List.perm_replicate.mp repeated
  cases containsFalse with
  | inl firstFalse =>
      subst first
      cases same
  | inr secondFalse =>
      subst second
      cases same

private theorem resampleFirst_all_true_atom (head tail : Bool) :
    ((resampleFirst [head, tail]).map unorder
      (unorder_quotient_map (Space.discrete Bool)).measurable)
        (Set.singleton (unorder [true, true])) =
      ENNReal.add
        (ENNReal.mul (ENNReal.half ENNReal.one)
          (if unorder [false, tail] = unorder [true, true] then
            ENNReal.one else ENNReal.zero))
        (ENNReal.mul (ENNReal.half ENNReal.one)
          (if unorder [true, tail] = unorder [true, true] then
            ENNReal.one else ENNReal.zero)) := by
  classical
  let event := Set.preimage unorder (Set.singleton (unorder [true, true]))
  have eventMeasurable :
      (Space.list (Space.discrete Bool)).Measurable event :=
    (unorder_quotient_map (Space.discrete Bool)).measurable
      unorder_all_true_singleton_measurable
  rw [Measure.map_apply _ _ _ unorder_all_true_singleton_measurable,
    resampleFirst_cons,
    Measure.add_apply_measurable _ _ eventMeasurable,
    Measure.smul_apply_measurable _ _ eventMeasurable,
    Measure.smul_apply_measurable _ _ eventMeasurable,
    Measure.dirac_apply _ _ eventMeasurable,
    Measure.dirac_apply _ _ eventMeasurable]
  simp only [event, Set.preimage, Set.singleton]

/-- A valid label-dependent Markov step need not descend to unordered
configurations. Two presentations of one orbit have different image laws. -/
public theorem label_dependent_not_lumpable :
    ¬ resampleFirst.LumpsAlong unorder
      (unorder_quotient_map (Space.discrete Bool)).measurable := by
  classical
  intro lumps
  have same : unorder [true, false] = unorder [false, true] := by
    apply Quotient.sound
    exact (List.Perm.swap true false []).symm
  have imageLaws := lumps [true, false] [false, true] same
  have atom := congrArg
    (fun law : Measure (Space.unordered (Space.discrete Bool)) =>
      law (Set.singleton (unorder [true, true]))) imageLaws
  have leftFalse : unorder [false, false] ≠ unorder [true, true] :=
    unorder_with_false_ne_all_true false false (.inl rfl)
  have leftTrue : unorder [true, false] ≠ unorder [true, true] :=
    unorder_with_false_ne_all_true true false (.inr rfl)
  have rightFalse : unorder [false, true] ≠ unorder [true, true] :=
    unorder_with_false_ne_all_true false true (.inl rfl)
  have halfNonzero : ENNReal.half ENNReal.one ≠ ENNReal.zero :=
    ENNReal.half_ne_zero ENNReal.one_ne_zero
  -- Evaluate the two image laws on the measurable all-true orbit.
  -- The left transition misses it, while the right hits it with mass 1/2.
  rw [resampleFirst_all_true_atom, resampleFirst_all_true_atom] at atom
  have impossible : ENNReal.zero = ENNReal.half ENNReal.one := by
    simpa only [ite_eq_right leftFalse, ite_eq_right leftTrue, ite_eq_right rightFalse,
      ite_true, ENNReal.mul_zero, ENNReal.mul_one,
      ENNReal.zero_add] using atom
  exact halfNonzero impossible.symm

end
end Problib.Measure
