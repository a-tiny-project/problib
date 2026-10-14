module

public import Problib.Analysis.Gaussian.Network.Collapse
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Real.Grind

/-! Networks built a block of rows at a time.

A network's law is the left fold of its rows' append steps from the empty
list. Read as kernels, the fold over a block of rows is one kernel from the
prefix already drawn to the whole list (`restKernel`), so a network extended
by a block is its law bound against that kernel (`extend_law`). The block
kernel keeps the prefix it starts from (`restKernel_take`), which makes the
first `k` rows a network whose law is the marginal of the first `k`
coordinates (`take_law`).

Three moves on blocks follow:

- A word of adjacent swaps moves the last `m` nodes in front of the first `k`
  (`blockWord`, `permute_blockWord`). Reversing along it is L6a's
  `reverse_along`.
- Rows that ignore a front block read the rest of the list as before
  (`shiftRows`, `restKernel_shift`).
- Weighting a network by a function of its first `k` coordinates acts on its
  first `k` rows alone (`collapse_prefix`): when the prefix network collapses
  to `Z` times another network of the same length, the whole network collapses
  to `Z` times the network with that prefix replaced.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Measurable list maps -/

public theorem take_measurable (count : Nat) :
    MeasurableMap (Space.list borel) (Space.list borel) (List.take (α := Carrier) count) := by
  induction count with
  | zero =>
      have equal : List.take (α := Carrier) 0 = fun _ => [] := funext fun _ => rfl
      rw [equal]
      intro set measurable
      exact MeasurableMap.constant (Space.list borel) (Space.list borel) ([] : List Carrier)
          measurable
  | succ count induction =>
      have equal : List.take (α := Carrier) (count + 1) = fun values =>
          if values.length = 0 then [] else entry values 0 :: values.tail.take count := by
        funext values
        match values with
        | [] => rfl
        | first :: rest => simp [entry]
      rw [equal]
      apply MeasurableMap.ite
      · exact ListSpace.length_measurable borel (set := fun length => length = 0) trivial
      · exact MeasurableMap.constant (Space.list borel) (Space.list borel) ([] : List Carrier)
      · measurability [entry_measurable 0, induction, ListSpace.tail_measurable borel,
          ListSpace.cons_measurable borel]

public theorem drop_measurable (count : Nat) :
    MeasurableMap (Space.list borel) (Space.list borel) (List.drop (α := Carrier) count) := by
  induction count with
  | zero =>
      intro set measurable
      exact measurable
  | succ count induction =>
      have equal : List.drop (α := Carrier) (count + 1) = fun values => (values.drop count).tail :=
          by
        funext values
        rw [List.tail_drop]
      rw [equal]
      intro set measurable
      exact induction (ListSpace.tail_measurable borel measurable)

public theorem prepend_measurable (front : List Carrier) :
    MeasurableMap (Space.list borel) (Space.list borel) (fun values => front ++ values) := by
  induction front with
  | nil =>
      intro set measurable
      exact measurable
  | cons first front induction =>
      exact MeasurableMap.comp (ListSpace.cons_measurable borel)
        (Space.pair_measurable (MeasurableMap.constant _ borel first) induction)

/-- Appending is jointly measurable: a fold of `cons` over the front list. -/
public theorem append_measurable :
    MeasurableMap (Space.product (Space.list borel) (Space.list borel)) (Space.list borel)
      (fun pair : List Carrier × List Carrier => pair.1 ++ pair.2) := by
  have folded : MeasurableMap (Space.product (Space.list borel) (Space.list borel)) (Space.list
      borel)
      (fun pair : List Carrier × List Carrier =>
        pair.1.foldr (fun head rest => head :: rest) pair.2) :=
    ListSpace.fold_measurable (initial := fun back : List Carrier => back)
      (step := fun input : Carrier × (List Carrier × List Carrier) => input.1 :: input.2.1)
      (MeasurableMap.identity _)
      (MeasurableMap.comp (ListSpace.cons_measurable borel)
        (Space.pair_measurable (Space.first_measurable _ _)
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))))
  have equal : (fun pair : List Carrier × List Carrier =>
      pair.1.foldr (fun head rest => head :: rest) pair.2) = fun pair => pair.1 ++ pair.2 := by
    funext pair
    induction pair.1 with
    | nil => rfl
    | cons head front induction => rw [List.foldr_cons, induction, List.cons_append]
  rw [← equal]
  intro set measurable
  exact folded measurable

public theorem appendRight_measurable (back : List Carrier) :
    MeasurableMap (Space.list borel) (Space.list borel) (fun values => values ++ back) :=
  MeasurableMap.comp append_measurable
    (Space.pair_measurable (MeasurableMap.identity _) (MeasurableMap.constant _ _ back))

/-! ### Appending, as a kernel -/

public theorem snocAt_measurable (values : List Carrier) :
    MeasurableMap borel (Space.list borel) (fun value => snoc (values, value)) :=
  MeasurableMap.comp snoc_measurable (Kernel.pair_left_measurable values)

/-- Draw one node from a row given the prefix, and append it. -/
@[expose] public def Row.appendKernel (row : Row) : Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach row.kernel row.kernelSFinite).map snoc snoc_measurable

public theorem Row.appendKernel_apply (row : Row) (values : List Carrier) :
    row.appendKernel values =
      (row.kernel values).map (fun value => snoc (values, value)) (snocAt_measurable values) := by
  unfold Row.appendKernel
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

public theorem appendLaw_eq_bind (law : Measure (Space.list borel)) (row : Row) :
    appendLaw law row = law.bind row.appendKernel := by
  unfold appendLaw Measure.semiproduct Row.appendKernel
  rw [Measure.map_bind]

/-- The rows of a block drawn in order from a prefix, as one kernel. -/
@[expose] public def restKernel : List Row → Kernel (Space.list borel) (Space.list borel)
  | [] => Kernel.deterministic (fun values => values) (MeasurableMap.identity (Space.list borel))
  | row :: rows => row.appendKernel.comp (restKernel rows)

public theorem foldl_appendLaw (rows : List Row) (law : Measure (Space.list borel)) :
    rows.foldl appendLaw law = law.bind (restKernel rows) := by
  induction rows generalizing law with
  | nil =>
      rw [List.foldl_nil, restKernel, Measure.bind_deterministic, Measure.map_id]
      exact MeasurableMap.identity _
  | cons row rows induction =>
      rw [List.foldl_cons, induction, appendLaw_eq_bind, Measure.bind_assoc]
      rfl

/-- The block drawn from a prefix, at one prefix. -/
@[expose] public def restLaw (rows : List Row) (values : List Carrier) :
    Measure (Space.list borel) :=
  restKernel rows values

public theorem restLaw_eq_foldl (rows : List Row) (values : List Carrier) :
    restLaw rows values = rows.foldl appendLaw (Measure.dirac _ values) := by
  rw [foldl_appendLaw, Measure.dirac_bind]
  rfl

public theorem restKernel_isProbability (rows : List Row) (values : List Carrier) :
    Measure.IsProbability (restKernel rows values) := by
  induction rows generalizing values with
  | nil => exact Measure.IsProbability.dirac _ _
  | cons row rows induction =>
      rw [restKernel, Kernel.comp_apply, Row.appendKernel_apply]
      exact Measure.IsProbability.bind
        (Measure.IsProbability.map (row.kernel_isProbability values) _ _) _ fun _ => induction _

/-- The block keeps every coordinate of the prefix it starts from. -/
public theorem restKernel_take (rows : List Row) {count : Nat} {values : List Carrier}
    (long : count ≤ values.length) :
    (restKernel rows values).map (List.take count) (take_measurable count) =
      Measure.dirac _ (values.take count) := by
  induction rows generalizing values with
  | nil =>
      rw [restKernel, Kernel.deterministic_apply, Measure.map_dirac]
      exact MeasurableMap.identity _
  | cons row rows induction =>
      rw [restKernel, Kernel.comp_apply, Measure.map_bind, Row.appendKernel_apply,
        Measure.bind_map]
      have pointwise : ∀ value : Carrier,
          (restKernel rows (snoc (values, value))).map (List.take count) (take_measurable count) =
            Measure.dirac _ (values.take count) := by
        intro value
        rw [induction (by simp [snoc]; omega)]
        congr 1
        exact List.take_append_of_le_length long
      have constant : ((restKernel rows).map (List.take count) (take_measurable count)).precomp
          (fun value => snoc (values, value)) (snocAt_measurable values) =
            Kernel.const borel (Measure.dirac _ (values.take count)) :=
        Kernel.ext fun value => pointwise value
      rw [constant, Measure.bind_const, (row.kernel_isProbability values).univ_eq_one,
        Measure.one_smul]

/-! ### Extending a network by a block -/

/-- Rows that extend a network of `start` nodes: row `j` of the block holds
`start + j` coefficients. -/
@[expose] public def TriangularFrom (start : Nat) (rows : List Row) : Prop :=
  ∀ (index : Nat) (row : Row), rows[index]? = some row → row.coefficients.length = start + index

namespace Network

/-- Append a block of rows. -/
@[expose] public def extend (network : Network) (rows : List Row)
    (triangular : TriangularFrom network.length rows)
    (positive : ∀ row ∈ rows, lt zero row.variance) : Network where
  rows := network.rows ++ rows
  triangular index row found := by
    rcases Nat.lt_or_ge index network.rows.length with below | above
    · rw [List.getElem?_append_left below] at found
      exact network.triangular index row found
    · rw [List.getElem?_append_right above] at found
      rw [triangular _ row found]
      unfold length
      omega
  positive row member := by
    rcases List.mem_append.mp member with old | new
    · exact network.positive row old
    · exact positive row new

@[simp] public theorem length_extend (network : Network) (rows : List Row) (triangular positive) :
    (network.extend rows triangular positive).length = network.length + rows.length := by
  simp [extend, length]

/-- A network extended by a block draws the block after its own law. -/
public theorem extend_law (network : Network) (rows : List Row) (triangular positive) :
    (network.extend rows triangular positive).law = network.law.bind (restKernel rows) := by
  unfold extend Network.law
  rw [List.foldl_append, foldl_appendLaw]

/-- The first `k` rows. -/
@[expose] public def take (network : Network) (count : Nat) : Network where
  rows := network.rows.take count
  triangular index row found := by
    rw [List.getElem?_take] at found
    split at found
    · exact network.triangular index row found
    · cases found
  positive row member := network.positive row (List.mem_of_mem_take member)

public theorem length_take (network : Network) (count : Nat) :
    (network.take count).length = min count network.length := by
  simp [take, length]

/-- The rows after the first `k`, as a block extending them. -/
public theorem drop_triangular (network : Network) {count : Nat} (long : count ≤ network.length) :
    TriangularFrom (network.take count).length (network.rows.drop count) := by
  intro index row found
  rw [List.getElem?_drop] at found
  rw [network.triangular _ row found, length_take, Nat.min_eq_left long]

public theorem take_extend (network : Network) {count : Nat} (long : count ≤ network.length) :
    (network.take count).extend (network.rows.drop count) (network.drop_triangular long)
      (fun row member => network.positive row (List.mem_of_mem_drop member)) = network :=
  ext (List.take_append_drop count network.rows)

/-- The first `k` rows draw the first `k` coordinates. -/
public theorem take_law (network : Network) (count : Nat) :
    network.law.map (List.take count) (take_measurable count) = (network.take count).law := by
  rcases Nat.lt_or_ge network.length count with short | long
  · have whole : network.take count = network := ext (List.take_of_length_le (Nat.le_of_lt short))
    rw [whole]
    apply (Measure.map_congr_on _ network.law_length_null _ (MeasurableMap.identity _) ?_).trans
      (Measure.map_id _)
    intro values counted
    change values.length = network.length at counted
    exact List.take_of_length_le (by omega)
  · conv => lhs; rw [← network.take_extend long]
    rw [extend_law, Measure.map_bind]
    have lengths := (network.take count).law_length_null
    rw [length_take, Nat.min_eq_left long] at lengths
    apply (Measure.bind_congr_ae _ (right := Kernel.deterministic (fun values => values)
      (MeasurableMap.identity _)) ?_).trans (by rw [Measure.bind_deterministic, Measure.map_id])
    apply Measure.AE.mono lengths
    intro values counted
    change (restKernel _ values).map _ _ = Measure.dirac _ values
    rw [restKernel_take _ (Nat.le_of_eq counted.symm), List.take_of_length_le (Nat.le_of_eq
        counted)]

public theorem replace_triangular (network : Network) {count : Nat} (front : Network)
    (length : front.length = count) : TriangularFrom front.length (network.rows.drop count) := by
  intro index row found
  rw [List.getElem?_drop] at found
  rw [network.triangular _ row found, length]

/-- The first `k` rows replaced by a network of `k` nodes. -/
@[expose] public def replacePrefix (network : Network) (count : Nat) (front : Network)
    (length : front.length = count) : Network :=
  front.extend (network.rows.drop count) (network.replace_triangular front length)
    (fun row member => network.positive row (List.mem_of_mem_drop member))

@[simp] public theorem length_replacePrefix (network : Network) (count : Nat) (front : Network)
    (length : front.length = count) (long : count ≤ network.length) :
    (network.replacePrefix count front length).length = network.length := by
  change (front.rows ++ network.rows.drop count).length = network.rows.length
  rw [List.length_append, List.length_drop]
  unfold Network.length at long length
  omega

public theorem take_replacePrefix (network : Network) (count : Nat) (front : Network)
    (length : front.length = count) :
    (network.replacePrefix count front length).take count = front := by
  apply ext
  change (front.rows ++ network.rows.drop count).take count = front.rows
  rw [List.take_append_of_le_length (by unfold Network.length at length; omega)]
  exact List.take_of_length_le (by unfold Network.length at length; omega)

end Network

/-! ### The block keeps its prefix, exactly -/

/-- Every list the block draws from `x` is `x` followed by what it drew. -/
public theorem restKernel_prefix (rows : List Row) (front : List Carrier) :
    ∀ tail : List Carrier,
      (restKernel rows (front ++ tail)).map (fun values => front ++ values.drop front.length)
          (MeasurableMap.comp (prepend_measurable front) (drop_measurable front.length)) =
        restKernel rows (front ++ tail) := by
  induction rows with
  | nil =>
      intro tail
      rw [restKernel, Kernel.deterministic_apply, Measure.map_dirac, List.drop_left]
      exact MeasurableMap.identity _
  | cons row rows induction =>
      intro tail
      rw [restKernel, Kernel.comp_apply, Measure.map_bind, Row.appendKernel_apply, Measure.bind_map,
        Measure.bind_map]
      congr 1
      apply Kernel.ext
      intro value
      change (restKernel rows (snoc (front ++ tail, value))).map _ _ =
        restKernel rows (snoc (front ++ tail, value))
      have rebased : snoc (front ++ tail, value) = front ++ (tail ++ [value]) := by
        simp [snoc]
      rw [rebased]
      exact induction (tail ++ [value])

/-- Weighting by a function of the prefix commutes with drawing the block. -/
public theorem bind_withDensity_prefix (law : Measure (Space.list borel)) (rows : List Row)
    {count : Nat} (lengths : law (fun values => values.length ≠ count) = ENNReal.zero)
    {density : List Carrier → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.list borel) density) :
    (law.bind (restKernel rows)).withDensity (fun values => density (values.take count)) =
      (law.withDensity density).bind (restKernel rows) := by
  have prefixMeasurable : ENNRealMeasurable (Space.list borel)
      (fun values : List Carrier => density (values.take count)) :=
    ENNRealMeasurable.comp densityMeasurable (take_measurable count)
  refine (Measure.eq_iff_lintegral _ _).mpr fun integrand integrandMeasurable => ?_
  rw [lintegral_withDensity _ prefixMeasurable integrandMeasurable,
    Measure.lintegral_bind _ _ (ENNRealMeasurable.mul prefixMeasurable integrandMeasurable),
    Measure.lintegral_bind _ _ integrandMeasurable,
    lintegral_withDensity _ densityMeasurable
      ((restKernel rows).lintegral_measurable integrandMeasurable)]
  apply lintegral_congr_ae
  apply Measure.AE.mono lengths
  intro front counted
  change lintegral (restKernel rows front)
      (fun values => ENNReal.mul (density (values.take count)) (integrand values)) =
    ENNReal.mul (density front) (lintegral (restKernel rows front) integrand)
  have shift : MeasurableMap (Space.list borel) (Space.list borel)
      (fun values => front ++ values.drop front.length) :=
    MeasurableMap.comp (prepend_measurable front) (drop_measurable front.length)
  have whole := restKernel_prefix rows front []
  rw [List.append_nil] at whole
  rw [← whole, lintegral_map _ _ shift (ENNRealMeasurable.mul prefixMeasurable integrandMeasurable),
    lintegral_map _ _ shift integrandMeasurable]
  have taken : ∀ values : List Carrier, (front ++ values.drop front.length).take count = front :=
    fun values => by
      rw [List.take_append_of_le_length (by omega)]
      exact List.take_of_length_le (by omega)
  simp only [taken]
  exact lintegral_smul _ _ (ENNRealMeasurable.comp integrandMeasurable shift)

namespace Network

/-- Weighting a network by a function of its first `k` coordinates collapses
its first `k` rows and keeps the rest. -/
public theorem collapse_prefix (network : Network) {count : Nat} (long : count ≤ network.length)
    (front : Network) (length : front.length = count) {density : List Carrier → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.list borel) density) (scalar : ENNReal)
    (collapse : (network.take count).law.withDensity density = Measure.smul scalar front.law) :
    network.law.withDensity (fun values => density (values.take count)) =
      Measure.smul scalar (network.replacePrefix count front length).law := by
  have lengths := (network.take count).law_length_null
  rw [length_take, Nat.min_eq_left long] at lengths
  conv => lhs; rw [← network.take_extend long]
  rw [extend_law, bind_withDensity_prefix _ _ lengths densityMeasurable, collapse,
    Measure.smul_bind]
  exact congrArg (Measure.smul scalar) (front.extend_law _ _ _).symm

end Network

/-! ### Moving a block in front -/

/-- `front ++ back` reads `front ++ zeros` as `back` would. -/
public theorem dot_append_append {left right front back : List Carrier}
    (counted : left.length = front.length) :
    dot (left ++ right) (front ++ back) = add (dot left front) (dot right back) := by
  induction left generalizing front with
  | nil =>
      cases front with
      | nil =>
          change dot right back = add zero (dot right back)
          real_grind
      | cons _ _ => cases counted
  | cons coefficient left induction =>
      cases front with
      | nil => cases counted
      | cons value front =>
          change add (mul coefficient value) (dot (left ++ right) (front ++ back)) =
            add (add (mul coefficient value) (dot left front)) (dot right back)
          rw [induction (by simpa using counted)]
          real_grind

public theorem dot_replicate_zero (count : Nat) (values : List Carrier) :
    dot (List.replicate count zero) values = zero := by
  induction count generalizing values with
  | zero => exact dot_nil_left values
  | succ count induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          change add (mul zero value) (dot (List.replicate count zero) values) = zero
          rw [induction]
          real_grind

/-- A row reading `count` more nodes in front, with zero coefficients. -/
@[expose] public def Row.shift (count : Nat) (row : Row) : Row where
  intercept := row.intercept
  coefficients := List.replicate count zero ++ row.coefficients
  variance := row.variance

public theorem Row.shift_mean (count : Nat) (row : Row) {front : List Carrier}
    (counted : front.length = count) (values : List Carrier) :
    (row.shift count).mean (front ++ values) = row.mean values := by
  unfold Row.mean Row.shift
  rw [dot_append_append (by simp [counted]), dot_replicate_zero]
  change add row.intercept (add zero (dot row.coefficients values)) = _
  real_grind

/-- Rows reading `count` more nodes in front, with zero coefficients. -/
@[expose] public def shiftRows (count : Nat) (rows : List Row) : List Row :=
  rows.map (Row.shift count)

/-- Rows shifted past a front block draw what the rows draw, behind it. -/
public theorem restKernel_shift (rows : List Row) {front : List Carrier} {count : Nat}
    (counted : front.length = count) (values : List Carrier) :
    restKernel (shiftRows count rows) (front ++ values) =
      (restKernel rows values).map (fun current => front ++ current) (prepend_measurable front) :=
          by
  induction rows generalizing values with
  | nil =>
      simp only [shiftRows, List.map_nil, restKernel]
      change Measure.dirac _ (front ++ values) = (Measure.dirac _ values).map _ _
      rw [Measure.map_dirac]
  | cons row rows induction =>
      simp only [shiftRows, List.map_cons, restKernel, Kernel.comp_apply]
      rw [Row.appendKernel_apply, Row.appendKernel_apply, Measure.bind_map, Measure.bind_map,
        Measure.map_bind]
      have kernels : (row.shift count).kernel (front ++ values) = row.kernel values := by
        rw [Row.kernel_apply, Row.kernel_apply, Row.shift_mean count row counted]
        rfl
      rw [kernels]
      congr 1
      apply Kernel.ext
      intro value
      change restKernel (shiftRows count rows) (snoc (front ++ values, value)) =
        (restKernel rows (snoc (values, value))).map _ _
      have rebased : snoc (front ++ values, value) = front ++ snoc (values, value) := by
        simp [snoc]
      rw [rebased]
      exact induction _

public theorem shiftRows_triangular {start count : Nat} {rows : List Row}
    (triangular : TriangularFrom start rows) : TriangularFrom (count + start) (shiftRows count
        rows) := by
  intro index row found
  rw [shiftRows, List.getElem?_map] at found
  cases inner : rows[index]? with
  | none => rw [inner] at found; cases found
  | some original =>
      rw [inner, Option.map_some, Option.some.injEq] at found
      subst found
      change (List.replicate count zero ++ original.coefficients).length = _
      rw [List.length_append, List.length_replicate, triangular index original inner]
      omega

/-- The word `[n - 1, …, 0]` shifted to start at position `j`. -/
public theorem permute_map_add {α : Type} (word : List Nat) (front values : List α) :
    permute (word.map (· + front.length)) (front ++ values) = front ++ permute word values := by
  induction word generalizing values with
  | nil => rfl
  | cons index word induction =>
      rw [List.map_cons, permute_cons, permute_cons, ← induction]
      congr 1
      clear induction
      induction front with
      | nil => rfl
      | cons first front inner =>
          change swapAt (index + front.length + 1) (first :: (front ++ values)) = _
          rw [show index + front.length + 1 = (index + front.length) + 1 from rfl]
          simp only [swapAt, List.cons_append, inner]

/-- Adjacent swaps that move the last `m` entries in front of the first `k`,
keeping the order within each block. -/
@[expose] public def blockWord (count : Nat) : Nat → List Nat
  | 0 => []
  | moved + 1 => frontWord count ++ (blockWord count moved).map (· + 1)

public theorem permute_blockWord {α : Type} {count moved : Nat} (front back : List α)
    (frontCounted : front.length = count) (backCounted : back.length = moved) :
    permute (blockWord count moved) (front ++ back) = back ++ front := by
  induction moved generalizing back with
  | zero =>
      rw [List.length_eq_zero_iff] at backCounted
      subst backCounted
      simp [blockWord]
  | succ moved induction =>
      match back, backCounted with
      | value :: rest, backCounted =>
          rw [blockWord, permute, List.foldl_append, ← permute, ← permute,
            permute_frontWord value rest frontCounted]
          have shifted := permute_map_add (blockWord count moved) [value] (front ++ rest)
          simp only [List.length_singleton, List.singleton_append] at shifted
          rw [shifted, induction rest (by simpa using backCounted)]
          rfl

end
end Problib.Analysis.Gaussian
