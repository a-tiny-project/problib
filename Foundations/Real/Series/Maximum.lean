module

public import Foundations.Real.Extended.Lattice
public import Foundations.Real.Extended.Indexed

set_option autoImplicit false

namespace Foundations.Real.ENNReal

/-- Finite prefix maxima of a sequence of extended nonnegative real numbers. -/
@[expose] public noncomputable def prefixMax (values : Nat → ENNReal) : Nat → ENNReal
  | 0 => values 0
  | stage + 1 => max (prefixMax values stage) (values (stage + 1))

public theorem prefixMaxStep (values : Nat → ENNReal) (stage : Nat) :
    le (prefixMax values stage) (prefixMax values (stage + 1)) :=
  leMaxLeft _ _

public theorem lePrefixMax (values : Nat → ENNReal) (index : Nat) :
    le (values index) (prefixMax values index) := by
  cases index with
  | zero => exact leRefl _
  | succ index => exact leMaxRight _ _

public theorem prefixMaxLeISup (values : Nat → ENNReal) (stage : Nat) :
    le (prefixMax values stage) (iSup values) := by
  induction stage with
  | zero => exact leISup values 0
  | succ stage induction => exact maxLe induction (leISup values (stage + 1))

/-- Countable supremum of prefix maxima equals the supremum of the original
sequence. -/
public theorem iSupPrefixMax (values : Nat → ENNReal) :
    iSup (prefixMax values) = iSup values := by
  apply leAntisymm (iSupLe (prefixMaxLeISup values))
  exact iSupLe (fun index => leTrans (lePrefixMax values index) (leISup _ index))

end Foundations.Real.ENNReal
