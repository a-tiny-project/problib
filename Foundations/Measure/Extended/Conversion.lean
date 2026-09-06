module

public import Foundations.Measure.Real.Borel
public import Foundations.Measure.Extended.Order
public import Foundations.Real.Extended.Conversion

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

/-- `ENNReal.ofReal` is Borel measurable on all signed real inputs. -/
public theorem ofRealMeasurable : ENNRealMeasurable borel ENNReal.ofReal := by
  intro threshold
  cases threshold with
  | top =>
      have same : Set.preimage ENNReal.ofReal (ennrealIoi ENNReal.top) = Set.empty := by
        apply Set.ext
        intro value
        exact ⟨fun member => member.2 (ENNReal.leTop _), False.elim⟩
      rw [same]
      exact borel.empty
  | finite threshold =>
      have same : Set.preimage ENNReal.ofReal (ennrealIoi (ENNReal.finite threshold)) =
          Ioi threshold.val := by
        apply Set.ext
        intro value
        have below := @ENNReal.ofRealLeIffLeToReal value (ENNReal.finite threshold) True.intro
        constructor
        · intro member
          exact notLeIffLt.mp (fun included => member.2 (below.mpr included))
        · intro member
          have reverse : ¬ENNReal.le (ENNReal.ofReal value) (ENNReal.finite threshold) :=
            fun included => member.2 (below.mp included)
          rcases ENNReal.leTotal (ENNReal.finite threshold) (ENNReal.ofReal value) with
            forward | backward
          · exact ⟨forward, reverse⟩
          · exact False.elim (reverse backward)
      rw [same]
      exact measurable_Ioi threshold.val

/-- The conversion from extended nonnegative reals to Dedekind reals is
measurable from the extended Borel space to the real Borel space. -/
public theorem toRealMeasurable : MeasurableMap ennrealBorel borel ENNReal.toReal := by
  apply measurableMap_borel_iff_Iic.mpr
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
            exact Or.inl ((ENNReal.leOfRealIffToRealLe
              (lower := ENNReal.finite value) True.intro nonnegative).mpr included)
          · intro member
            rcases member with included | impossible
            · exact (ENNReal.leOfRealIffToRealLe
                (lower := ENNReal.finite value) True.intro nonnegative).mp included
            · exact False.elim (ENNReal.finiteNeTop value impossible)
    rw [same]
    exact ennrealBorel.union (ENNRealMeasurable.identity.iic _)
      (ENNRealMeasurable.identity.singleton _)
  · have same : Set.preimage ENNReal.toReal (Iic upper) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun included => nonnegative
        (Dedekind.leTrans (ENNReal.toRealNonnegative value) included), False.elim⟩
    rw [same]
    exact ennrealBorel.empty

end Foundations.Measure.Real
