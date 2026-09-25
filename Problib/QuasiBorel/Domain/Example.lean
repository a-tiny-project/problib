module

public import Problib.QuasiBorel.Domain.FixedPoint
public import Problib.Domain.Necessity

namespace Problib.QuasiBorel.Domain.Example

public section

universe u

open Problib.Domain

variable {Ω : Type u} (source : Source Ω)

@[expose] def grow : Hom (Predomain.powerset source Nat) (Predomain.powerset source Nat) :=
  ⟨⟨Necessity.grow, fun _ => True.intro⟩, Necessity.grow_continuous⟩

@[expose] def powerset_pointed : Pointed (Predomain.powerset source Nat).order :=
  Pointed.powerset Nat

 theorem powerset_nontrivial :
    (Pointed.powerset Nat).bottom ≠ (fun _ : Nat => True) := by
  intro h
  have bad : (Pointed.powerset Nat).bottom 0 := h.symm ▸ True.intro
  exact bad

 theorem grow_fix_all (n : Nat) :
    Predomain.fix (Predomain.powerset source Nat) (Pointed.powerset Nat) (grow source) n := by
  rw [Predomain.fix_apply]
  exact Necessity.grow_fix_all n

 theorem grow_finite_approximants (k n : Nat) :
    Predomain.iterateHom (Predomain.powerset source Nat) (Pointed.powerset Nat)
      k (grow source) n ↔ n < k := by
  rw [Predomain.iterateHom_apply]
  exact Necessity.iterate_grow k n

 theorem grow_fix_not_finite_stage (k : Nat) :
    Predomain.fix (Predomain.powerset source Nat) (Pointed.powerset Nat) (grow source) ≠
    Predomain.iterateHom (Predomain.powerset source Nat) (Pointed.powerset Nat) k (grow source) := by
  intro h
  have finite := h ▸ grow_fix_all source k
  exact Nat.lt_irrefl k ((grow_finite_approximants source k k).mp finite)

end

end Problib.QuasiBorel.Domain.Example
