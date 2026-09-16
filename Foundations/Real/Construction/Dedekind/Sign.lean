module

import all Foundations.Real.Construction.Dedekind.Order

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Sign.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only the rational boundary facts needed to close nonnegative
multiplication. Names and namespaces change.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Cut

theorem nonnegativeOfNonnegativeCutNotMem {cut : Cut} {outside : Rat}
    (nonnegative : 0 ≤ cut) (absent : ¬cut.mem outside) :
    0 ≤ outside := by
  by_cases outsideNegative : outside < 0
  · exact False.elim (absent (nonnegative outside outsideNegative))
  · exact Rat.not_lt.mp outsideNegative

theorem positiveOfPositiveMemOfNotMem {cut : Cut} {inside outside : Rat}
    (member : cut.mem inside) (insidePositive : 0 < inside)
    (absent : ¬cut.mem outside) :
    0 < outside :=
  Rational.ltOfLtOfLe insidePositive
    (cut.leOfMemOfNotMem member absent)

end Cut

end Foundations.Real.Construction.Dedekind
