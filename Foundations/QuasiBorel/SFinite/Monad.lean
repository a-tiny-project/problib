module

public import Foundations.QuasiBorel.SFinite.Bind

set_option autoImplicit false

/-!
# Monad laws for s-finite quasi-Borel spaces

This module establishes the monad laws, zero laws, and functor laws for the
s-finite quasi-Borel space monad.
It proves Kleisli and bind unit and associativity laws, preservation of the
zero law, and functor identity and composition equations.
-/
namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v w

variable {domain codomain : Space realSource}

/-- Proves the right unit law for Kleisli extension along the Dirac unit. -/
theorem extend_unit_right (space : Space realSource) :
    extend (unit space) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  apply Law.ext
  change law.val.bind (toKernel (unit space)) = law.val
  rw [toKernel_unit, Measure.bind_deterministic, Measure.map_id]

/-- Proves the left unit law for Kleisli extension precomposed with the Dirac unit. -/
theorem extend_unit_left (kernel : Hom domain (object codomain)) :
    Hom.comp (extend kernel) (unit domain) = kernel := by
  apply Hom.ext
  intro point
  apply Law.ext
  exact Measure.dirac_bind point (toKernel kernel)

/-- Proves associativity for Kleisli extensions of law-valued morphisms. -/
theorem extend_assoc {result : Space realSource}
    (first : Hom domain (object codomain)) (second : Hom codomain (object result)) :
    Hom.comp (extend second) (extend first) = extend (Hom.comp (extend second) first) := by
  apply Hom.ext
  intro law
  apply Law.ext
  change (law.val.bind (toKernel first)).bind (toKernel second) =
    law.val.bind (toKernel (Hom.comp (extend second) first))
  rw [Measure.bind_assoc, toKernel_extend_comp]

/-- Proves the left unit law for monadic bind against a pure Dirac law. -/
@[simp] theorem pure_bind (point : domain.Carrier) (kernel : Hom domain (object codomain)) :
    bind (pure domain point) kernel = kernel point :=
  congrArg (fun morphism => morphism point) (extend_unit_left kernel)

/-- Proves the right unit law for monadic bind against the Dirac unit. -/
@[simp] theorem bind_unit (law : Law domain) : bind law (unit domain) = law :=
  congrArg (fun morphism => morphism law) (extend_unit_right domain)

/-- Proves associativity for nested monadic binds. -/
theorem bind_assoc {result : Space realSource} (law : Law domain)
    (first : Hom domain (object codomain)) (second : Hom codomain (object result)) :
    bind (bind law first) second = bind law (Hom.comp (extend second) first) :=
  congrArg (fun morphism => morphism law) (extend_assoc first second)

/-- Proves that binding the zero law produces the zero law. -/
@[simp] theorem zero_bind (kernel : Hom domain (object codomain)) :
    bind (zero domain) kernel = zero codomain := by
  apply Law.ext
  exact Measure.zero_bind (toKernel kernel)

/-- Proves that binding any law against the constant zero morphism produces the zero law. -/
@[simp] theorem bind_zero (law : Law domain) :
    bind law (Hom.constant domain (object codomain) (zero codomain)) = zero codomain := by
  apply Law.ext
  have equal : toKernel (Hom.constant domain (object codomain) (zero codomain)) =
      Kernel.zero domain.toMeasurable codomain.toMeasurable := by
    apply Kernel.ext
    intro point
    rfl
  rw [bind_val, equal, Measure.bind_zero]
  rfl

/-- Functorial pushforward of laws along a quasi-Borel morphism. -/
@[expose] noncomputable def map (function : Hom domain codomain) :
    Hom (object domain) (object codomain) :=
  extend (Hom.comp (unit codomain) function)

/-- Proves that functorial map agrees with the pushforward measure. -/
theorem map_val (function : Hom domain codomain) (law : Law domain) :
    (map function law).val = law.val.map function function.toMeasurable := by
  have equal : toKernel (Hom.comp (unit codomain) function) =
      Kernel.deterministic function function.toMeasurable := by
    apply Kernel.ext
    intro point
    rfl
  change law.val.bind (toKernel (Hom.comp (unit codomain) function)) = _
  rw [equal, Measure.bind_deterministic]

/-- Proves that mapping the identity morphism preserves laws. -/
theorem map_id (space : Space realSource) :
    map (Hom.identity space) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  apply Law.ext
  rw [map_val]
  exact Measure.map_id law.val

/-- Proves that mapping a composite morphism equals the composition of mappings. -/
theorem map_comp {result : Space realSource}
    (after : Hom codomain result) (before : Hom domain codomain) :
    map (Hom.comp after before) = Hom.comp (map after) (map before) := by
  apply Hom.ext
  intro law
  apply Law.ext
  change (map (Hom.comp after before) law).val = (map after (map before law)).val
  rw [map_val, map_val, map_val]
  exact (Measure.map_comp law.val before after before.toMeasurable after.toMeasurable).symm

/-- Proves that mapping preserves pure Dirac laws. -/
@[simp] theorem map_pure (function : Hom domain codomain) (point : domain.Carrier) :
    map function (pure domain point) = pure codomain (function point) := by
  apply Law.ext
  rw [map_val]
  exact Measure.map_dirac function function.toMeasurable point

/-- Proves that mapping preserves the zero law. -/
@[simp] theorem map_zero (function : Hom domain codomain) :
    map function (zero domain) = zero codomain := by
  apply Law.ext
  rw [map_val]
  exact Measure.map_zero function function.toMeasurable

/-- Proves the pushforward-bind exchange law for functorial map and monadic bind. -/
theorem bind_map {result : Space realSource} (law : Law domain)
    (function : Hom domain codomain) (kernel : Hom codomain (object result)) :
    bind (map function law) kernel = bind law (Hom.comp kernel function) := by
  apply Law.ext
  rw [bind_val, map_val, Measure.bind_map, bind_val]
  rfl

/-- Proves naturality of functorial map distributed over monadic bind. -/
theorem map_bind {result : Space realSource} (function : Hom codomain result)
    (law : Law domain) (kernel : Hom domain (object codomain)) :
    map function (bind law kernel) = bind law (Hom.comp (map function) kernel) := by
  apply Law.ext
  rw [map_val, bind_val, Measure.map_bind, bind_val]
  apply congrArg (fun next => law.val.bind next)
  apply Kernel.ext
  intro point
  exact (map_val function (kernel point)).symm

/-- Proves that functorial pushforward preserves the total measure on the universal set. -/
theorem map_univ (function : Hom domain codomain) (law : Law domain) :
    (map function law).val Set.univ = law.val Set.univ := by
  rw [map_val, Measure.map_apply _ _ _ (by exact codomain.toMeasurable.univ)]
  rfl

end

end Foundations.QuasiBorel.SFinite
