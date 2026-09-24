module

public import Problib.Real.Extended.Lattice
public import Problib.Real.Extended.Indexed

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Finite prefix maxima of a sequence of extended nonnegative real numbers. -/
@[expose] public noncomputable def prefixMax (values : Nat → ENNReal) : Nat → ENNReal
  | 0 => values 0
  | stage + 1 => max (prefixMax values stage) (values (stage + 1))

public theorem prefixMax_step (values : Nat → ENNReal) (stage : Nat) :
    le (prefixMax values stage) (prefixMax values (stage + 1)) :=
  le_max_left _ _

public theorem le_prefixMax (values : Nat → ENNReal) (index : Nat) :
    le (values index) (prefixMax values index) := by
  cases index with
  | zero => exact le_refl _
  | succ index => exact le_max_right _ _

public theorem prefixMax_le_iSup (values : Nat → ENNReal) (stage : Nat) :
    le (prefixMax values stage) (iSup values) := by
  induction stage with
  | zero => exact le_iSup values 0
  | succ stage induction => exact max_le induction (le_iSup values (stage + 1))

/-- Countable supremum of prefix maxima equals the supremum of the original
sequence. -/
public theorem iSup_prefixMax (values : Nat → ENNReal) :
    iSup (prefixMax values) = iSup values := by
  apply le_antisymm (iSup_le (prefixMax_le_iSup values))
  exact iSup_le (fun index => le_trans (le_prefixMax values index) (le_iSup _ index))

end Problib.Real.ENNReal
