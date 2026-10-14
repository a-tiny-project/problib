module

public import Problib.Measure.Kernel.Pi.Law
public import Problib.Measure.Kernel.Product
import Problib.Measure.Kernel.Product.Transport
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# Reading a product law at repeated keys

Read a product law at finitely many keys, some of them repeated. The values
read have the law of one independent draw per position, each position reading
the draw at the first position with its key. A repeated key reads one draw, and
the draws at its later positions go unused.

`first` names that representative: it keeps each position's key, and positions
with one key share one representative. The proof restricts both sides to the
representatives, where the keys are distinct, so both are products with the
same laws, and spreads the representatives back over every position.

`lintegral_read` reads one key lazily. A quantity of the table and its value
at a key, which ignores the table's own value at that key once the read value
is given, integrates as a fresh draw from the key's law followed by the table.
It is `update` read through Tonelli.
-/

namespace Problib.Measure.Pi

open Problib.Real

universe u v

public section

variable {ι : Type u} {α : Type v} {space : Space α}

namespace IsProduct

variable {measure : Measure (Space.pi fun _ : ι => space)} {laws : ι → Measure space}

/-- Reading a product at finitely many keys, some of them repeated, has the law
of one independent draw per position read at each key's first position.
`first` sends a position to a representative of its key: it keeps the key, and
positions with one key share one representative. -/
theorem reads_mixed {n : Nat} (product : IsProduct measure laws) (keys : Fin n → ι)
    (first : Fin n → Fin n) (same : ∀ position, keys (first position) = keys position)
    (shared : ∀ position other, keys position = keys other → first position = first other)
    {draws : Measure (Space.pi fun _ : Fin n => space)}
    {laneLaws : Fin n → Measure space} (drawsProduct : IsProduct draws laneLaws)
    (agreeAt : ∀ position, first position = position → laneLaws position = laws (keys position)) :
    measure.map (fun point position => point (keys position))
        (Space.pi_reindex (fun _ : ι => space) keys) =
      draws.map (fun point position => point (first position))
        (Space.pi_reindex (fun _ : Fin n => space) first) := by
  have settled : ∀ position, first (first position) = first position :=
    fun position => shared _ _ (same position)
  let representative : Fin n → {position : Fin n // first position = position} :=
    fun position => ⟨first position, settled position⟩
  let encode : {position : Fin n // first position = position} → ι :=
    fun chosen => keys chosen.1
  have injective : Function.Injective encode := by
    intro chosen other equal
    apply Subtype.ext
    rw [← chosen.2, ← other.2]
    exact shared _ _ equal
  have agree := ext (product.reindex encode injective)
    ((drawsProduct.reindex (fun chosen => chosen.1) fun _ _ equal => Subtype.ext equal).congr_laws
      fun chosen => agreeAt chosen.1 chosen.2)
  calc measure.map (fun point position => point (keys position))
          (Space.pi_reindex (fun _ : ι => space) keys)
      = (measure.map (fun point chosen => point (encode chosen))
          (Space.pi_reindex (fun _ : ι => space) encode)).map
          (fun point position => point (representative position))
          (Space.pi_reindex (fun _ : {position : Fin n // first position = position} => space)
            representative) := by
        rw [Measure.map_comp]

        exact Measure.map_congr_function _ _ _ (funext fun point => funext fun position =>
          congrArg point (same position).symm)
    _ = (draws.map
          (fun point (chosen : {position : Fin n // first position = position}) => point chosen.1)
          (Space.pi_reindex (fun _ : Fin n => space)
            fun chosen : {position : Fin n // first position = position} => chosen.1)).map
          (fun point position => point (representative position))
          (Space.pi_reindex (fun _ : {position : Fin n // first position = position} => space)
            representative) := by
        rw [agree]
    _ = draws.map (fun point position => point (first position))
          (Space.pi_reindex (fun _ : Fin n => space) first) := by
        rw [Measure.map_comp]

/-- Uniform draws are the special case where unused lanes keep their laws. -/
theorem reads {n : Nat} (product : IsProduct measure laws) (keys : Fin n → ι)
    (first : Fin n → Fin n) (same : ∀ position, keys (first position) = keys position)
    (shared : ∀ position other, keys position = keys other → first position = first other)
    {draws : Measure (Space.pi fun _ : Fin n => space)}
    (drawsProduct : IsProduct draws fun position => laws (keys position)) :
    measure.map (fun point position => point (keys position))
        (Space.pi_reindex (fun _ : ι => space) keys) =
      draws.map (fun point position => point (first position))
        (Space.pi_reindex (fun _ : Fin n => space) first) :=
  reads_mixed product keys first same shared drawsProduct fun _ _ => rfl

/-- Reading a product at one key is a fresh draw from that key's law when the
rest of the integrand ignores the table's value at the key. -/
theorem lintegral_read (product : IsProduct measure laws) (key : ι)
    (measureFinite : Measure.SFinite measure) (lawFinite : Measure.SFinite (laws key))
    {function : α × (ι → α) → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product space (Space.pi fun _ : ι => space)) function)
    (hidden : ∀ value point, function (value, replace point key value) = function (value, point)) :
    lintegral measure (fun point => function (point key, point)) =
      lintegral (laws key) fun value => lintegral measure fun point => function (value, point) := by
  have readMeasurable : ENNRealMeasurable (Space.pi fun _ : ι => space)
      (fun point => function (point key, point)) :=
    ENNRealMeasurable.comp functionMeasurable
      (Space.pair_measurable (Space.coordinate_measurable (fun _ : ι => space) key)
        (MeasurableMap.identity _))
  have swappedMeasurable : ENNRealMeasurable
      (Space.product (Space.pi fun _ : ι => space) space)
      (fun pair => function (pair.2, pair.1)) :=
    ENNRealMeasurable.comp functionMeasurable (Space.swap_measurable _ _)
  calc lintegral measure (fun point => function (point key, point))
      = lintegral ((Measure.prod measure (laws key) lawFinite).map
          (fun pair => replace pair.1 key pair.2) (replace_measurable key))
          (fun point => function (point key, point)) := by
        rw [product.update key lawFinite]
    _ = lintegral (Measure.prod measure (laws key) lawFinite)
          (fun pair => function (pair.2, pair.1)) := by
        rw [lintegral_map _ _ _ readMeasurable]
        congr 1
        funext pair
        rw [replace_same, hidden]
    _ = lintegral (laws key) fun value => lintegral measure fun point => function (value, point) :=
        lintegral_prod_symm measure (laws key) measureFinite lawFinite swappedMeasurable

end IsProduct

end

end Problib.Measure.Pi
