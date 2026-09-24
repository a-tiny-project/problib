module

set_option autoImplicit false

namespace Problib.QuasiBorel

universe u

public structure Source (Ω : Type u) where
  Measurable : (Ω → Ω) → Prop
  Partition : (Ω → Nat) → Prop
  identity : Measurable (fun value => value)
  constant : ∀ value, Measurable (fun _ => value)
  comp : ∀ {first second}, Measurable first → Measurable second →
    Measurable (fun value => second (first value))
  partition_reparam : ∀ {partition reparam}, Partition partition → Measurable reparam →
    Partition (fun value => partition (reparam value))
  piecewise : ∀ {partition : Ω → Nat} {branches : Nat → Ω → Ω},
    Partition partition → (∀ index, Measurable (branches index)) →
      Measurable (fun value => branches (partition value) value)

namespace Source

@[expose] public def unrestricted (Ω : Type u) : Source Ω where
  Measurable := fun _ => True
  Partition := fun _ => True
  identity := True.intro
  constant := fun _ => True.intro
  comp := fun _ _ => True.intro
  partition_reparam := fun _ _ => True.intro
  piecewise := fun _ _ => True.intro

end Source

end Problib.QuasiBorel
