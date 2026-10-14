module

public import Problib.Measure.Real.Borel
public import Problib.Measure.Extended.Order
public import Problib.Real.Extended.Conversion

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

/-- `ENNReal.ofReal` is Borel measurable on all signed real inputs. -/
public theorem ofReal_measurable : ENNRealMeasurable borel ENNReal.ofReal := by
  intro threshold
  cases threshold with
  | top =>
      have same : Set.preimage ENNReal.ofReal (ennrealIoi ENNReal.top) = Set.empty := by
        apply Set.ext
        intro value
        exact ⟨fun member => member.2 (ENNReal.le_top _), False.elim⟩
      rw [same]
      exact borel.empty
  | finite threshold =>
      have same : Set.preimage ENNReal.ofReal (ennrealIoi (ENNReal.finite threshold)) =
          Ioi threshold.val := by
        apply Set.ext
        intro value
        have below := @ENNReal.ofReal_le_iff_le_toReal value (ENNReal.finite threshold) True.intro
        constructor
        · intro member
          exact not_le_iff_lt.mp (fun included => member.2 (below.mpr included))
        · intro member
          have reverse : ¬ENNReal.le (ENNReal.ofReal value) (ENNReal.finite threshold) :=
            fun included => member.2 (below.mp included)
          rcases ENNReal.le_total (ENNReal.finite threshold) (ENNReal.ofReal value) with
            forward | backward
          · exact ⟨forward, reverse⟩
          · exact False.elim (reverse backward)
      rw [same]
      exact measurable_ioi threshold.val

/-- The conversion from extended nonnegative reals to Dedekind reals is
measurable from the extended Borel space to the real Borel space. -/
public theorem toReal_measurable : MeasurableMap ennrealBorel borel ENNReal.toReal := by
  apply measurableMap_borel_iff_iic.mpr
  intro upper
  by_cases nonnegative : Dedekind.le Dedekind.zero upper
  · have same : Set.preimage ENNReal.toReal (Iic upper) =
        Set.union (ennrealIic (ENNReal.ofReal upper)) (ennrealSingleton ENNReal.top) := by
      apply Set.ext
      intro value
      cases value with
      | top =>
          exact ⟨fun _ => Or.inr rfl, fun _ => nonnegative⟩
      | finite value =>
          constructor
          · intro included
            exact Or.inl ((ENNReal.le_ofReal_iff_toReal_le
              (lower := ENNReal.finite value) True.intro nonnegative).mpr included)
          · intro member
            rcases member with included | impossible
            · exact (ENNReal.le_ofReal_iff_toReal_le
                (lower := ENNReal.finite value) True.intro nonnegative).mp included
            · exact False.elim (ENNReal.finite_ne_top value impossible)
    rw [same]
    exact ennrealBorel.union (ENNRealMeasurable.identity.iic _)
      (ENNRealMeasurable.identity.singleton _)
  · have same : Set.preimage ENNReal.toReal (Iic upper) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun included => nonnegative
        (Dedekind.le_trans (ENNReal.toReal_nonnegative value) included), False.elim⟩
    rw [same]
    exact ennrealBorel.empty

end Problib.Measure.Real
