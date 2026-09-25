namespace Problib.Inference.Trace

universe u

def AlmostEverywherePairwise {Trace : Type u}
    (almostEverywhere : ((Trace × Trace) → Prop) → Prop)
    (pairwise : Trace → Trace → Prop) : Prop :=
  almostEverywhere fun pair => pairwise pair.1 pair.2

/--
The explicit premise needed to turn an almost-everywhere trace property into
the pointwise support property used by a deterministic split operation.
-/
structure SupportBridge {Trace : Type u}
    (almostEverywhere : ((Trace × Trace) → Prop) → Prop)
    (pairwise : Trace → Trace → Prop)
    (support : Trace → Prop) : Prop where
  toPointwise :
    AlmostEverywherePairwise almostEverywhere pairwise →
      ∀ {left right}, support left → support right → pairwise left right

end Problib.Inference.Trace
