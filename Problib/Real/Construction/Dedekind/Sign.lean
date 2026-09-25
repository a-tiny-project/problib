module

import all Problib.Real.Construction.Dedekind.Order

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Sign.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only the rational boundary facts needed to close nonnegative
multiplication. Names and namespaces change.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

theorem nonnegative_of_nonnegative_cut_not_mem {cut : Cut} {outside : Rat}
    (nonnegative : 0 ≤ cut) (absent : ¬cut.mem outside) :
    0 ≤ outside := by
  by_cases outsideNegative : outside < 0
  · exact False.elim (absent (nonnegative outside outsideNegative))
  · exact Rat.not_lt.mp outsideNegative

theorem positive_of_positive_mem_of_not_mem {cut : Cut} {inside outside : Rat}
    (member : cut.mem inside) (insidePositive : 0 < inside)
    (absent : ¬cut.mem outside) :
    0 < outside :=
  Rational.lt_of_lt_of_le insidePositive
    (cut.le_of_mem_of_not_mem member absent)

end Cut

end Problib.Real.Construction.Dedekind
