module

public import Problib.Measure.Memo.Product
public import Problib.Measure.Kernel.Pi.Basic

set_option autoImplicit false

/-!
# Boolean memo tables are kernel products

The Boolean memo kernel decodes one seed into a whole table. Its law at each
input is the product of its body's laws at the keys, so it is the countable
product of its body, whichever randomizer builds that product.
-/

namespace Problib.Measure.Memo.Indexed
public section
open Problib.Real Problib.Measure.Real

universe u v
variable {κ : Type u} {α : Type v} {source : Space α} {keySpace : Space κ}

/-- The Boolean memo kernel's law at each input is the product of its body's
laws at the keys. -/
theorem ofBody_isProduct (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool))
    (probability : ∀ input, Measure.IsProbability (body input)) (input : α) :
    Pi.IsProduct (ofBody encode decode body input) fun key => body (key, input) := by
  have product := law_isProduct encode decode roundTrip (bodyBias body input)
  rw [← ofBody_apply encode decode body input] at product
  exact product.congr_laws fun key =>
    ofBody_coordinate encode decode roundTrip body probability input key

/-- The Boolean memo kernel is the countable product of its body. -/
theorem ofBody_eq_pi (encode : κ → Nat) (decode : Nat → Option κ)
    (roundTrip : ∀ key, decode (encode key) = some key)
    (body : Kernel (Space.product keySpace source) (Space.discrete Bool))
    (selection : Kernel.Randomizer body) :
    ofBody encode decode body = Kernel.pi encode selection :=
  Kernel.pi_unique encode (encode_injective encode decode roundTrip) selection
    (ofBody_isProduct encode decode roundTrip body selection.isProbability)

end
end Problib.Measure.Memo.Indexed
