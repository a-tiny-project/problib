module

public import Problib.Analysis.Gaussian.Network.Block
public import Problib.Analysis.Gaussian.Affine
import Problib.Real.Grind
import Problib.Measure.Measurability.Real

/-! An affine move with Gaussian network noise, as appended children.

A linear-Gaussian state moves by `x' = c + F x + w`, where the noise `w` is
drawn from a network `W` independently of `x`. Given `x`, the new state is
again a network: its node `i` regresses on the old state and on the new nodes
before it. Writing `w = x' − c − F x` into `W`'s row `i`, which reads
`w₍<ᵢ₎` with coefficients `Bᵢ`, gives the child row

- intercept `cᵢ + μᵢ − ⟨Bᵢ, c⟩`,
- coefficients `Fᵢ − Σ_{k<i} Bᵢₖ Fₖ` on the old state and `Bᵢ` on the new
  nodes before it,
- variance `dᵢ`, the noise row's own (`childRow`).

So a network extended by the children draws the old state, then the moved
state (`extend_childRows_law`). The proof is induction over the noise rows.
Each step is a translated Gaussian draw: the child's conditional mean at
`x ++ x'₍<ᵢ₎` is `(c + F x)ᵢ` plus the noise row's mean at `w₍<ᵢ₎`
(`childRow_mean`), and a Gaussian moved by a constant is the Gaussian at the
moved mean (`law_translate`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Affine maps on lists -/

/-- The affine map `x ↦ c + F x`, with offset `c` and matrix rows `F`. -/
public structure Affine where
  offset : List Carrier
  matrix : List (List Carrier)

namespace Affine

/-- `rows` outputs over `columns` inputs. -/
@[expose] public def Shaped (affine : Affine) (rows columns : Nat) : Prop :=
  affine.offset.length = rows ∧ affine.matrix.length = rows ∧
    ∀ row ∈ affine.matrix, row.length = columns

/-- `c + F x`. -/
@[expose] public def apply (affine : Affine) (values : List Carrier) : List Carrier :=
  List.zipWith (fun offset row => add offset (dot row values)) affine.offset affine.matrix

public theorem length_apply (affine : Affine) {rows columns : Nat}
    (shaped : affine.Shaped rows columns) (values : List Carrier) :
    (affine.apply values).length = rows := by
  unfold apply
  rw [List.length_zipWith, shaped.1, shaped.2.1, Nat.min_self]

end Affine

/-- Entrywise sum, over the shorter list. -/
@[expose] public def addLists (left right : List Carrier) : List Carrier :=
  List.zipWith add left right

public theorem addLists_concat {left right : List Carrier} (value : Carrier)
    (short : right.length < left.length) :
    addLists left (right ++ [value]) =
      addLists left right ++ [add (entry left right.length) value] := by
  induction right generalizing left with
  | nil =>
      match left, short with
      | first :: rest, _ => simp [addLists, entry]
  | cons head right induction =>
      match left, short with
      | first :: rest, short =>
          simp only [addLists, List.cons_append, List.zipWith_cons_cons, List.length_cons] at *
          rw [induction (by omega)]
          simp [entry]

/-! ### Linear algebra of `dot` -/

/-- `⟨b, u + w⟩ = ⟨b, u⟩ + ⟨b, w⟩` while both reach past `b`. -/
public theorem dot_addLists {coefficients left right : List Carrier}
    (leftLong : coefficients.length ≤ left.length)
    (rightLong : coefficients.length ≤ right.length) :
    dot coefficients (addLists left right) =
      add (dot coefficients left) (dot coefficients right) := by
  induction coefficients generalizing left right with
  | nil =>
      change zero = add zero zero
      real_grind
  | cons coefficient coefficients induction =>
      match left, right, leftLong, rightLong with
      | first :: left, second :: right, leftLong, rightLong =>
          change add (mul coefficient (add first second)) (dot coefficients (addLists left right)) =
            add (add (mul coefficient first) (dot coefficients left))
              (add (mul coefficient second) (dot coefficients right))
          rw [induction (by simpa using leftLong) (by simpa using rightLong)]
          real_grind

/-- `⟨b, c + F x⟩ = ⟨b, c⟩ + ⟨b, F x⟩` while `c` and `F` reach past `b`. -/
public theorem dot_apply (coefficients : List Carrier) (affine : Affine) (values : List Carrier)
    (offsetLong : coefficients.length ≤ affine.offset.length)
    (matrixLong : coefficients.length ≤ affine.matrix.length) :
    dot coefficients (affine.apply values) =
      add (dot coefficients affine.offset)
        (dot coefficients (affine.matrix.map fun row => dot row values)) := by
  obtain ⟨offset, matrix⟩ := affine
  change dot coefficients (List.zipWith _ offset matrix) = _
  simp only at offsetLong matrixLong ⊢
  induction coefficients generalizing offset matrix with
  | nil =>
      change zero = add zero zero
      real_grind
  | cons coefficient coefficients induction =>
      match offset, matrix, offsetLong, matrixLong with
      | first :: offset, row :: matrix, offsetLong, matrixLong =>
          change add (mul coefficient (add first (dot row values)))
              (dot coefficients (List.zipWith _ offset matrix)) =
            add (add (mul coefficient first) (dot coefficients offset))
              (add (mul coefficient (dot row values))
                (dot coefficients (matrix.map fun row => dot row values)))
          rw [induction offset matrix (by simpa using offsetLong) (by simpa using matrixLong)]
          real_grind

/-- `start − Σₖ bₖ Fₖ`, one `combine` per coefficient. -/
@[expose] public def mixRows (start : List Carrier) (coefficients : List Carrier)
    (rows : List (List Carrier)) : List Carrier :=
  (List.zip coefficients rows).foldl (fun current pair => combine (neg pair.1) current pair.2) start

public theorem length_mixRows {start : List Carrier} {columns : Nat} (counted : start.length =
    columns)
    (coefficients : List Carrier) {rows : List (List Carrier)}
    (shaped : ∀ row ∈ rows, row.length = columns) :
    (mixRows start coefficients rows).length = columns := by
  induction coefficients generalizing start rows with
  | nil => exact counted
  | cons coefficient coefficients induction =>
      cases rows with
      | nil => exact counted
      | cons row rows =>
          apply induction
          · rw [combine_length, counted, shaped row (List.mem_cons_self ..), Nat.min_self]
          · exact fun current member => shaped current (List.mem_cons_of_mem _ member)

public theorem dot_mixRows {start : List Carrier} {columns : Nat} (counted : start.length = columns)
    (coefficients : List Carrier) {rows : List (List Carrier)}
    (shaped : ∀ row ∈ rows, row.length = columns) (long : coefficients.length ≤ rows.length)
    (values : List Carrier) :
    dot (mixRows start coefficients rows) values =
      sub (dot start values) (dot coefficients (rows.map fun row => dot row values)) := by
  induction coefficients generalizing start rows with
  | nil =>
      change dot start values = sub (dot start values) zero
      real_grind
  | cons coefficient coefficients induction =>
      match rows, long with
      | row :: rows, long =>
          have rowCounted := shaped row (List.mem_cons_self ..)
          change dot (mixRows (combine (neg coefficient) start row) coefficients rows) values = _
          rw [induction (by rw [combine_length, counted, rowCounted, Nat.min_self])
            (fun current member => shaped current (List.mem_cons_of_mem _ member))
            (by simpa using long), dot_combine _ (counted.trans rowCounted.symm)]
          change _ = sub (dot start values) (add (mul coefficient (dot row values))
            (dot coefficients (rows.map fun row => dot row values)))
          real_grind

/-- A list cut or padded with zeros to `count` entries. -/
@[expose] public def resize (count : Nat) (values : List Carrier) : List Carrier :=
  values.take count ++ List.replicate (count - values.length) zero

@[simp] public theorem length_resize (count : Nat) (values : List Carrier) :
    (resize count values).length = count := by
  simp [resize]
  omega

public theorem resize_of_length {count : Nat} {values : List Carrier} (counted : values.length =
    count) :
    resize count values = values := by
  simp [resize, counted, List.take_of_length_le (Nat.le_of_eq counted)]

/-! ### The children -/

/-- The new node `i`: noise row `i` with `w = x' − c − F x` written in. -/
@[expose] public def childRow (affine : Affine) (columns index : Nat) (row : Row) : Row where
  intercept := add (entry affine.offset index) (sub row.intercept (dot row.coefficients
      affine.offset))
  coefficients :=
    resize columns (mixRows (affine.matrix.getD index []) row.coefficients affine.matrix) ++
      row.coefficients
  variance := row.variance

/-- The new state's rows, one per noise row. -/
@[expose] public def childRows (affine : Affine) (columns : Nat) (rows : List Row) : List Row :=
  rows.mapIdx (childRow affine columns)

public theorem childRows_concat (affine : Affine) (columns : Nat) (rows : List Row) (row : Row) :
    childRows affine columns (rows ++ [row]) =
      childRows affine columns rows ++ [childRow affine columns rows.length row] := by
  simp [childRows]

public theorem length_childRows (affine : Affine) (columns : Nat) (rows : List Row) :
    (childRows affine columns rows).length = rows.length := by
  simp [childRows]

public theorem childRows_triangular (affine : Affine) (columns : Nat) (noise : Network) :
    TriangularFrom columns (childRows affine columns noise.rows) := by
  intro index row found
  unfold childRows at found
  rw [List.getElem?_mapIdx] at found
  cases inner : noise.rows[index]? with
  | none => rw [inner] at found; cases found
  | some original =>
      rw [inner, Option.map_some, Option.some.injEq] at found
      subst found
      simp only [childRow, List.length_append, length_resize]
      rw [noise.triangular index original inner]

public theorem childRows_positive (affine : Affine) (columns : Nat) (noise : Network) :
    ∀ row ∈ childRows affine columns noise.rows, lt zero row.variance := by
  intro row member
  unfold childRows at member
  obtain ⟨index, found⟩ := List.getElem?_of_mem member
  rw [List.getElem?_mapIdx] at found
  cases inner : noise.rows[index]? with
  | none => rw [inner] at found; cases found
  | some original =>
      rw [inner, Option.map_some, Option.some.injEq] at found
      subst found
      exact noise.positive original (List.mem_of_getElem? inner)

/-- The child's conditional mean is the moved mean of the noise row:
`(c + F x)ᵢ + μᵢ + ⟨Bᵢ, w⟩` at `x ++ (c + F x + w)₍<ᵢ₎`. -/
public theorem childRow_mean (affine : Affine) {rows columns : Nat}
    (shaped : affine.Shaped rows columns) {index : Nat} (below : index < rows) (row : Row)
    (rowCounted : row.coefficients.length = index) {values noise : List Carrier}
    (valuesCounted : values.length = columns) (noiseCounted : noise.length = index) :
    (childRow affine columns index row).mean (values ++ addLists (affine.apply values) noise) =
      add (entry (affine.apply values) index) (row.mean noise) := by
  have matrixRow : (affine.matrix.getD index []).length = columns := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [shaped.2.1]; exact below)]
    exact shaped.2.2 _ (List.getElem_mem _)
  have mixedCounted := length_mixRows matrixRow row.coefficients shaped.2.2
  have applyLong : index ≤ (affine.apply values).length := by
    rw [affine.length_apply shaped]; omega
  unfold Row.mean childRow
  simp only
  rw [dot_append_append (by rw [length_resize, valuesCounted]), resize_of_length mixedCounted,
    dot_mixRows matrixRow row.coefficients shaped.2.2 (by rw [shaped.2.1]; omega),
    dot_addLists (by omega) (by omega),
    dot_apply _ _ _ (by rw [shaped.1]; omega) (by rw [shaped.2.1]; omega)]
  have entryApply : entry (affine.apply values) index =
      add (entry affine.offset index) (dot (affine.matrix.getD index []) values) := by
    unfold entry Affine.apply
    rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem (by rw [shaped.1]; exact below),
      List.getElem?_eq_getElem (by rw [shaped.2.1]; exact below)]
    simp [List.getElem?_eq_getElem (by rw [shaped.1]; exact below),
      List.getElem?_eq_getElem (by rw [shaped.2.1]; exact below)]
  rw [entryApply]
  real_grind

/-! ### The moved state's law -/

public theorem add_left_measurable (shift : Carrier) :
    MeasurableMap borel borel (fun value => add shift value) :=
  measurable_add (MeasurableMap.constant _ borel shift) (MeasurableMap.identity _)

/-- A Gaussian moved by a constant is the Gaussian at the moved mean. -/
public theorem law_translate (mean variance shift : Carrier) (positive : lt zero variance) :
    (Gaussian.law mean variance).map (fun value => add shift value) (add_left_measurable shift) =
      Gaussian.law (add shift mean) variance := by
  rw [← law_standard_variance mean variance positive, ← law_standard_variance _ variance positive,
    Measure.map_comp]
  apply Measure.map_congr_function
  funext value
  real_grind

/-- The moved state given the old one, appended to it: `x ++ (c + F x + w)`. -/
@[expose] public def movedAppend (affine : Affine) (values noise : List Carrier) : List Carrier :=
  values ++ addLists (affine.apply values) noise

public theorem addLists_measurable (left : List Carrier) :
    MeasurableMap (Space.list borel) (Space.list borel) (addLists left) := by
  induction left with
  | nil =>
      have equal : addLists [] = fun _ => [] := funext fun _ => rfl
      rw [equal]
      intro set measurable
      exact MeasurableMap.constant (Space.list borel) (Space.list borel) ([] : List Carrier)
          measurable
  | cons first left induction =>
      have equal : addLists (first :: left) = fun values =>
          if values.length = 0 then [] else add first (entry values 0) :: addLists left
              values.tail := by
        funext values
        match values with
        | [] => rfl
        | value :: rest => simp [addLists, entry]
      rw [equal]
      apply MeasurableMap.ite
      · exact ListSpace.length_measurable borel (set := fun length => length = 0) trivial
      · intro set measurable
        exact MeasurableMap.constant (Space.list borel) (Space.list borel) ([] : List Carrier)
            measurable
      · exact MeasurableMap.comp (ListSpace.cons_measurable borel)
          (Space.pair_measurable (MeasurableMap.comp (add_left_measurable first) (entry_measurable
              0))
            (MeasurableMap.comp induction (ListSpace.tail_measurable borel)))

public theorem movedAppend_measurable (affine : Affine) (values : List Carrier) :
    MeasurableMap (Space.list borel) (Space.list borel) (movedAppend affine values) :=
  MeasurableMap.comp (prepend_measurable values) (addLists_measurable _)

/-- Drawing the children from `x` draws the noise and moves it to `c + F x`. -/
public theorem restKernel_childRows (affine : Affine) {rows columns : Nat}
    (shaped : affine.Shaped rows columns) (noise : Network) (fits : noise.length ≤ rows)
    {values : List Carrier} (valuesCounted : values.length = columns) :
    restKernel (childRows affine columns noise.rows) values =
      noise.law.map (movedAppend affine values) (movedAppend_measurable affine values) := by
  induction noise using Network.induction with
  | empty network empty =>
      rw [empty, childRows, List.mapIdx_nil]
      change Measure.dirac _ values = _
      unfold Network.law
      rw [empty, List.foldl_nil, Measure.map_dirac]
      simp [movedAppend, addLists]
  | append network row rowShaped rowPositive induction =>
      have below : network.length < rows := by
        rw [Network.length_append] at fits; omega
      have previous := induction (Nat.le_of_lt below)
      change restKernel (childRows affine columns (network.rows ++ [row])) values = _
      rw [childRows_concat, ← restLaw, restLaw_eq_foldl, List.foldl_append, ← restLaw_eq_foldl,
        restLaw, previous, List.foldl_cons, List.foldl_nil, appendLaw_eq_bind, Measure.bind_map,
        Network.law_append, appendLaw_eq_bind, Measure.map_bind]
      apply Measure.bind_congr_ae
      apply Measure.AE.mono network.law_length_null
      intro current counted
      change (childRow affine columns network.rows.length row).appendKernel
          (movedAppend affine values current) =
        (row.appendKernel current).map (movedAppend affine values) _
      rw [Row.appendKernel_apply, Row.appendKernel_apply, Measure.map_comp, Row.kernel_apply,
        Row.kernel_apply]
      have meanEq : (childRow affine columns network.rows.length row).mean
          (movedAppend affine values current) =
            add (entry (affine.apply values) network.rows.length) (row.mean current) :=
        childRow_mean affine shaped (index := network.rows.length) below row rowShaped
          valuesCounted counted
      rw [meanEq]
      change (Gaussian.law _ row.variance).map _ _ = _
      rw [← law_translate _ _ _ rowPositive, Measure.map_comp]
      apply Measure.map_congr_function
      funext value
      simp only [snoc, movedAppend]
      rw [addLists_concat value (by rw [affine.length_apply shaped, counted]; exact below),
        List.append_assoc, counted]
      rfl

end
end Problib.Analysis.Gaussian
