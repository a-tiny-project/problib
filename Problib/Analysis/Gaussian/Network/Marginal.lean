module

public import Problib.Analysis.Gaussian.Network.Order

/-! Marginals of a linear-Gaussian network on a runtime subset of its nodes.

A subset is a mask `keep : List Bool`, one flag per node, so saying which nodes
are kept needs no index arithmetic. `select keep x` is the kept coordinates of
`x` in order, and `Network.marginal keep` is a network whose law is the
network's law pushed along `select keep` (`marginal_law`). Its mean is the
selected mean (`marginal_mean`), and at a mask of the network's length it has
one node per set flag (`length_marginal`).

The marginal drops one node at a time. `dropNode i` carries node `i` past
every later node by adjacent swaps (`sinkFrom`), each an exact reversal
(`reverse_along`), and then drops it as the last node (`marginal_last`). Its
law is the law pushed along erasing coordinate `i` (`dropNode_law`). The
marginal drops the masked nodes from the last to the first (`dropped`), so no
drop moves a node still to be dropped.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Erasing a coordinate -/

public theorem eraseIdx_measurable (index : Nat) :
    MeasurableMap (Space.list borel) (Space.list borel)
      (fun values : List Carrier => values.eraseIdx index) := by
  induction index with
  | zero =>
      have equal : (fun values : List Carrier => values.eraseIdx 0) = List.tail := by
        funext values
        cases values <;> rfl
      rw [equal]
      intro set measurable
      exact ListSpace.tail_measurable borel measurable
  | succ index induction =>
      have equal : (fun values : List Carrier => values.eraseIdx (index + 1)) = fun values =>
          if values.length = 0 then values else entry values 0 :: values.tail.eraseIdx index := by
        funext values
        match values with
        | [] => rfl
        | first :: rest => simp [entry]
      rw [equal]
      apply MeasurableMap.ite
      · exact ListSpace.length_measurable borel (set := fun length => length = 0) trivial
      · exact MeasurableMap.identity _
      · measurability [entry_measurable 0, induction, ListSpace.tail_measurable borel,
          ListSpace.cons_measurable borel]

/-- Erasing the coordinates of a word, left to right, is measurable. -/
public theorem eraseAll_measurable (word : List Nat) :
    MeasurableMap (Space.list borel) (Space.list borel)
      (fun values : List Carrier => word.foldl List.eraseIdx values) := by
  induction word with
  | nil =>
      intro set measurable
      exact measurable
  | cons index word induction =>
      intro set measurable
      exact eraseIdx_measurable index (induction measurable)

/-! ### Sinking a node -/

/-- The adjacent swaps that carry node `i` past every later node of `count`. -/
@[expose] public def sinkFrom (index count : Nat) : List Nat :=
  List.range' index (count - 1 - index)

private theorem range'_shift (start count : Nat) :
    List.range' (start + 1) count = (List.range' start count).map (· + 1) := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction => simp [List.range'_succ, induction]

private theorem permute_shift {α : Type} (word : List Nat) (first : α) (values : List α) :
    permute (word.map (· + 1)) (first :: values) = first :: permute word values := by
  induction word generalizing values with
  | nil => rfl
  | cons index word induction => exact induction (swapAt index values)

private theorem permute_sinkHead {α : Type} :
    ∀ (first : α) (values : List α),
      permute (List.range' 0 values.length) (first :: values) = values ++ [first]
  | _, [] => rfl
  | first, second :: rest => by
      rw [List.length_cons, List.range'_succ, permute_cons, range'_shift]
      change permute ((List.range' 0 rest.length).map (· + 1)) (second :: first :: rest) = _
      rw [permute_shift, permute_sinkHead first rest]
      rfl

/-- Sinking node `i` leaves the other coordinates in order and puts `xᵢ` last. -/
public theorem permute_sinkFrom {α : Type} :
    ∀ (index : Nat) (values : List α) (below : index < values.length),
      permute (sinkFrom index values.length) values = values.eraseIdx index ++ [values[index]]
  | 0, first :: rest, _ => by
      unfold sinkFrom
      rw [show (first :: rest).length - 1 - 0 = rest.length by simp]
      exact permute_sinkHead first rest
  | index + 1, first :: rest, below => by
      have shifted : sinkFrom (index + 1) (first :: rest).length =
          (sinkFrom index rest.length).map (· + 1) := by
        unfold sinkFrom
        rw [show (first :: rest).length - 1 - (index + 1) = rest.length - 1 - index by
          simp only [List.length_cons]; omega, range'_shift]
      rw [shifted, permute_shift,
        permute_sinkFrom index rest (by simp only [List.length_cons] at below; omega)]
      rfl

namespace Network

/-! ### Dropping one node -/

/-- Mean of the initial part: the mean without its last entry. -/
public theorem mean_init (network : Network) : network.init.mean = network.mean.dropLast := by
  by_cases empty : network.rows = []
  · simp [mean, init, empty]
  · obtain ⟨shaped, positive, rebuilt⟩ := network.append_init_last empty
    calc network.init.mean
        = (meanAppend network.init.mean (network.rows.getLast empty)).dropLast := by
          rw [meanAppend, List.dropLast_concat]
      _ = (network.init.append _ shaped positive).mean.dropLast := by rw [mean_append]
      _ = network.mean.dropLast := by rw [rebuilt]

/-- Drop node `i`: sink it past every later node, then drop the last node. A
network with no node `i` is unchanged. -/
@[expose] public def dropNode (network : Network) (index : Nat) : Network :=
  if index < network.length then (network.reverseAlong (sinkFrom index network.length)).init
  else network

/-- Dropping node `i` marginalizes coordinate `i`. -/
public theorem dropNode_law (network : Network) (index : Nat) :
    network.law.map (fun values => values.eraseIdx index) (eraseIdx_measurable index) =
      (network.dropNode index).law := by
  unfold dropNode
  split
  · rename_i below
    rw [← Network.marginal_last _ (by rw [length_reverseAlong]; omega), ← Network.reverse_along,
      Measure.map_comp]
    apply Measure.map_congr_on _ network.law_length_null
    intro values counted
    change values.length = network.length at counted
    change values.eraseIdx index = (permute (sinkFrom index network.length) values).dropLast
    rw [← counted, permute_sinkFrom index values (by omega), List.dropLast_concat]
  · rename_i above
    rw [Measure.map_congr_on _ network.law_length_null (eraseIdx_measurable index)
      (MeasurableMap.identity _) fun values counted =>
        List.eraseIdx_of_length_le (by change values.length = network.length at counted; omega)]
    exact Measure.map_id _

public theorem dropNode_mean (network : Network) (index : Nat) :
    (network.dropNode index).mean = network.mean.eraseIdx index := by
  unfold dropNode
  split
  · rename_i below
    rw [mean_init, reverseAlong_mean, ← network.shape.1,
      permute_sinkFrom index network.mean (by rw [network.shape.1]; exact below),
      List.dropLast_concat]
  · rename_i above
    exact (List.eraseIdx_of_length_le (by rw [network.shape.1]; omega)).symm

/-- Dropping the nodes of a word, left to right, marginalizes their
coordinates in turn. -/
public theorem dropAll_law (word : List Nat) (network : Network) :
    network.law.map (fun values => word.foldl List.eraseIdx values) (eraseAll_measurable word) =
      (word.foldl dropNode network).law := by
  induction word generalizing network with
  | nil => exact Measure.map_id _
  | cons index word induction =>
      rw [List.foldl_cons, ← induction, ← network.dropNode_law index, Measure.map_comp]
      rfl

public theorem dropAll_mean (word : List Nat) (network : Network) :
    (word.foldl dropNode network).mean = word.foldl List.eraseIdx network.mean := by
  induction word generalizing network with
  | nil => rfl
  | cons index word induction =>
      rw [List.foldl_cons, induction, dropNode_mean]
      rfl

end Network

/-! ### The kept coordinates -/

/-- The coordinates of `x` whose flag is set, in order. Coordinates past the
mask's end are kept. -/
@[expose] public def select : List Bool → List Carrier → List Carrier
  | [], values => values
  | _ :: _, [] => []
  | true :: keep, value :: values => value :: select keep values
  | false :: keep, _ :: values => select keep values

/-- The positions whose flag is clear, ascending, counted from `start`. -/
@[expose] public def droppedFrom : List Bool → Nat → List Nat
  | [], _ => []
  | true :: keep, start => droppedFrom keep (start + 1)
  | false :: keep, start => start :: droppedFrom keep (start + 1)

/-- The positions whose flag is clear, last first. -/
@[expose] public def dropped (keep : List Bool) : List Nat := (droppedFrom keep 0).reverse

private theorem droppedFrom_succ (keep : List Bool) (start : Nat) :
    droppedFrom keep (start + 1) = (droppedFrom keep start).map (· + 1) := by
  induction keep generalizing start with
  | nil => rfl
  | cons flag keep induction => cases flag <;> simp [droppedFrom, induction]

private theorem eraseAll_shift (word : List Nat) (first : Carrier) (values : List Carrier) :
    (word.map (· + 1)).foldl List.eraseIdx (first :: values) =
      first :: word.foldl List.eraseIdx values := by
  induction word generalizing values with
  | nil => rfl
  | cons index word induction => exact induction (values.eraseIdx index)

private theorem eraseAll_nil (word : List Nat) : word.foldl List.eraseIdx ([] : List Carrier) = [] := by
  induction word with
  | nil => rfl
  | cons index word induction => exact induction

/-- Selecting is erasing the dropped positions, last first. -/
public theorem select_eq_eraseAll (keep : List Bool) (values : List Carrier) :
    select keep values = (dropped keep).foldl List.eraseIdx values := by
  induction keep generalizing values with
  | nil => rfl
  | cons flag keep induction =>
      cases values with
      | nil => cases flag <;> exact (eraseAll_nil _).symm
      | cons value values =>
          cases flag
          · simp only [select, dropped, droppedFrom, List.reverse_cons, List.foldl_append,
              droppedFrom_succ, ← List.map_reverse, eraseAll_shift, List.foldl_cons, List.foldl_nil,
              List.eraseIdx_cons_zero]
            exact induction values
          · simp only [select, dropped, droppedFrom, droppedFrom_succ, ← List.map_reverse,
              eraseAll_shift]
            rw [induction values]
            rfl

public theorem select_measurable (keep : List Bool) :
    MeasurableMap (Space.list borel) (Space.list borel) (select keep) := by
  rw [show select keep = fun values => (dropped keep).foldl List.eraseIdx values from
    funext (select_eq_eraseAll keep)]
  exact eraseAll_measurable _

/-- At a mask of its length, a list keeps one coordinate per set flag. -/
public theorem length_select :
    ∀ (keep : List Bool) (values : List Carrier), keep.length = values.length →
      (select keep values).length = (keep.filter id).length
  | [], [], _ => rfl
  | true :: keep, _ :: values, length => by
      simp only [select, List.length_cons, List.filter_cons_of_pos (show id true = true from rfl)]
      rw [length_select keep values (by simpa using length)]
  | false :: keep, _ :: values, length => by
      simp only [select, List.filter_cons_of_neg (show ¬id false = true from Bool.false_ne_true)]
      exact length_select keep values (by simpa using length)

namespace Network

/-- The marginal on the nodes whose flag is set. -/
@[expose] public def marginal (network : Network) (keep : List Bool) : Network :=
  (dropped keep).foldl dropNode network

/-- The law of the kept coordinates is the marginal network's law. -/
public theorem marginal_law (network : Network) (keep : List Bool) :
    network.law.map (select keep) (select_measurable keep) = (network.marginal keep).law := by
  rw [Measure.map_congr_function _ _ (eraseAll_measurable (dropped keep))
    (funext (select_eq_eraseAll keep))]
  exact dropAll_law _ _

public theorem marginal_mean (network : Network) (keep : List Bool) :
    (network.marginal keep).mean = select keep network.mean := by
  rw [select_eq_eraseAll]
  exact dropAll_mean _ _

/-- At a mask of the network's length, the marginal has one node per set flag. -/
public theorem length_marginal (network : Network) (keep : List Bool)
    (length : keep.length = network.length) :
    (network.marginal keep).length = (keep.filter id).length := by
  rw [← (network.marginal keep).shape.1, marginal_mean]
  exact length_select keep network.mean (length.trans network.shape.1.symm)

end Network

end

end Problib.Analysis.Gaussian
