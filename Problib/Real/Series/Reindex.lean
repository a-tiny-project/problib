module

public import Problib.Countable.Bijection
public import Problib.Real.Series.Convergence

set_option autoImplicit false

namespace Problib.Real.ENNReal

private def reindexMatrix (equivalence : Countable.Bijection Nat Nat)
    (values : Nat → ENNReal) (row column : Nat) : ENNReal :=
  if column = equivalence.forward row then values column else zero

public theorem tsum_reindex (equivalence : Countable.Bijection Nat Nat)
    (values : Nat → ENNReal) :
    tsum (fun index => values (equivalence.forward index)) =
      tsum values := by
  have rowEvaluation (row : Nat) :
      tsum (fun column => reindexMatrix equivalence values row column) =
        values (equivalence.forward row) := by
    have equal :
        (fun column => reindexMatrix equivalence values row column) =
          single (equivalence.forward row)
            (values (equivalence.forward row)) := by
      funext column
      by_cases mapped : column = equivalence.forward row
      · rw [mapped]
        simp [reindexMatrix, single]
      · simp [reindexMatrix, single, mapped]
    rw [equal, tsum_single]
  have columnEvaluation (column : Nat) :
      tsum (fun row => reindexMatrix equivalence values row column) =
        values column := by
    have equal :
        (fun row => reindexMatrix equivalence values row column) =
          single (equivalence.inverse column) (values column) := by
      funext row
      by_cases atIndex : row = equivalence.inverse column
      · subst row
        unfold reindexMatrix single
        rw [equivalence.forward_inverse]
        simp
      · have notMapped : column ≠ equivalence.forward row := by
          intro mapped
          apply atIndex
          exact (equivalence.inverse_forward row).symm.trans
            (congrArg equivalence.inverse mapped.symm)
        simp [reindexMatrix, single, atIndex, notMapped]
    rw [equal, tsum_single]
  calc
    tsum (fun index => values (equivalence.forward index)) =
        tsum (fun row =>
          tsum (fun column =>
            reindexMatrix equivalence values row column)) := by
      apply tsum_congr
      intro row
      exact (rowEvaluation row).symm
    _ = tsum (fun column =>
        tsum (fun row =>
          reindexMatrix equivalence values row column)) :=
      tsum_comm (reindexMatrix equivalence values)
    _ = tsum values := by
      apply tsum_congr
      exact columnEvaluation

@[expose] public def flatten (values : Nat → Nat → ENNReal) :
    Nat → ENNReal :=
  fun index =>
    let pair := Countable.Pair.decode index
    values pair.1 pair.2

private def encodedEntry (values : Nat → Nat → ENNReal)
    (row column flatIndex : Nat) : ENNReal :=
  if flatIndex = Countable.Pair.encode (row, column) then
    values row column
  else
    zero

private def rowSlice (values : Nat → Nat → ENNReal)
    (row flatIndex : Nat) : ENNReal :=
  if (Countable.Pair.decode flatIndex).1 = row then
    flatten values flatIndex
  else
    zero

private theorem encodedEntry_column_evaluation
    (values : Nat → Nat → ENNReal) (row column : Nat) :
    tsum (fun flatIndex => encodedEntry values row column flatIndex) =
      values row column := by
  have equal :
      (fun flatIndex => encodedEntry values row column flatIndex) =
        single (Countable.Pair.encode (row, column))
          (values row column) := by
    funext flatIndex
    simp [encodedEntry, single]
  rw [equal, tsum_single]

private theorem encodedEntry_flat_evaluation
    (values : Nat → Nat → ENNReal) (row flatIndex : Nat) :
    tsum (fun column => encodedEntry values row column flatIndex) =
      rowSlice values row flatIndex := by
  by_cases belongs : (Countable.Pair.decode flatIndex).1 = row
  · have equal :
        (fun column => encodedEntry values row column flatIndex) =
          single (Countable.Pair.decode flatIndex).2
            (flatten values flatIndex) := by
      funext column
      by_cases atIndex :
          column = (Countable.Pair.decode flatIndex).2
      · subst column
        have pairEqual :
            (row, (Countable.Pair.decode flatIndex).2) =
              Countable.Pair.decode flatIndex := by
          apply Prod.ext
          · exact belongs.symm
          · rfl
        have encoded :
            Countable.Pair.encode
                (row, (Countable.Pair.decode flatIndex).2) =
              flatIndex := by
          rw [pairEqual, Countable.Pair.encode_decode]
        unfold encodedEntry single flatten
        rw [if_pos encoded.symm, if_pos rfl]
        change values row (Countable.Pair.decode flatIndex).2 =
          values (Countable.Pair.decode flatIndex).1
            (Countable.Pair.decode flatIndex).2
        rw [belongs]
      · have notEncoded :
            flatIndex ≠ Countable.Pair.encode (row, column) := by
          intro encoded
          have decodedEqual :
              Countable.Pair.decode flatIndex = (row, column) := by
            rw [encoded, Countable.Pair.decode_encode]
          have secondEqual :
              (Countable.Pair.decode flatIndex).2 = column :=
            congrArg Prod.snd decodedEqual
          exact atIndex secondEqual.symm
        simp [encodedEntry, single, atIndex, notEncoded]
    rw [equal, tsum_single]
    simp [rowSlice, belongs]
  · have allZero : ∀ column,
        encodedEntry values row column flatIndex = zero := by
      intro column
      have notEncoded :
          flatIndex ≠ Countable.Pair.encode (row, column) := by
        intro encoded
        apply belongs
        have decodedEqual :
            Countable.Pair.decode flatIndex = (row, column) := by
          rw [encoded, Countable.Pair.decode_encode]
        exact congrArg Prod.fst decodedEqual
      simp [encodedEntry, notEncoded]
    calc
      tsum (fun column => encodedEntry values row column flatIndex) =
          tsum (fun _ => zero) := tsum_congr allZero
      _ = zero := tsum_zero
      _ = rowSlice values row flatIndex := by
        simp [rowSlice, belongs]

private theorem rowSlice_evaluation (values : Nat → Nat → ENNReal)
    (row : Nat) :
    tsum (rowSlice values row) = tsum (values row) := by
  calc
    tsum (rowSlice values row) =
        tsum (fun flatIndex =>
          tsum (fun column =>
            encodedEntry values row column flatIndex)) := by
      apply tsum_congr
      intro flatIndex
      exact (encodedEntry_flat_evaluation values row flatIndex).symm
    _ = tsum (fun column =>
        tsum (fun flatIndex =>
          encodedEntry values row column flatIndex)) :=
      (tsum_comm (fun column flatIndex =>
        encodedEntry values row column flatIndex)).symm
    _ = tsum (values row) := by
      apply tsum_congr
      exact encodedEntry_column_evaluation values row

private theorem row_partition_evaluation
    (values : Nat → Nat → ENNReal) (flatIndex : Nat) :
    tsum (fun row => rowSlice values row flatIndex) =
      flatten values flatIndex := by
  have equal :
      (fun row => rowSlice values row flatIndex) =
        single (Countable.Pair.decode flatIndex).1
          (flatten values flatIndex) := by
    funext row
    by_cases atIndex : row = (Countable.Pair.decode flatIndex).1
    · subst row
      simp [rowSlice, single]
    · have reverse :
          (Countable.Pair.decode flatIndex).1 ≠ row :=
        fun equal => atIndex equal.symm
      simp [rowSlice, single, atIndex, reverse]
  rw [equal, tsum_single]

public theorem tsum_flatten (values : Nat → Nat → ENNReal) :
    tsum (flatten values) = tsum (fun row => tsum (values row)) := by
  calc
    tsum (flatten values) =
        tsum (fun flatIndex =>
          tsum (fun row => rowSlice values row flatIndex)) := by
      apply tsum_congr
      intro flatIndex
      exact (row_partition_evaluation values flatIndex).symm
    _ = tsum (fun row => tsum (rowSlice values row)) :=
      (tsum_comm (rowSlice values)).symm
    _ = tsum (fun row => tsum (values row)) := by
      apply tsum_congr
      exact rowSlice_evaluation values

end Problib.Real.ENNReal
