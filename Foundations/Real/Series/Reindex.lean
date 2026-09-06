module

public import Foundations.Real.Series.Bijection
public import Foundations.Real.Series.Convergence

set_option autoImplicit false

namespace Foundations.Real.ENNReal

private def reindexMatrix (equivalence : Bijection Nat Nat)
    (values : Nat → ENNReal) (row column : Nat) : ENNReal :=
  if column = equivalence.forward row then values column else zero

public theorem tsumReindex (equivalence : Bijection Nat Nat)
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
    rw [equal, tsumSingle]
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
        rw [equivalence.forwardInverse]
        simp
      · have notMapped : column ≠ equivalence.forward row := by
          intro mapped
          apply atIndex
          exact (equivalence.inverseForward row).symm.trans
            (congrArg equivalence.inverse mapped.symm)
        simp [reindexMatrix, single, atIndex, notMapped]
    rw [equal, tsumSingle]
  calc
    tsum (fun index => values (equivalence.forward index)) =
        tsum (fun row =>
          tsum (fun column =>
            reindexMatrix equivalence values row column)) := by
      apply tsumCongr
      intro row
      exact (rowEvaluation row).symm
    _ = tsum (fun column =>
        tsum (fun row =>
          reindexMatrix equivalence values row column)) :=
      tsumComm (reindexMatrix equivalence values)
    _ = tsum values := by
      apply tsumCongr
      exact columnEvaluation

@[expose] public def flatten (values : Nat → Nat → ENNReal) :
    Nat → ENNReal :=
  fun index =>
    let pair := NatProductBijection.decode index
    values pair.1 pair.2

private def encodedEntry (values : Nat → Nat → ENNReal)
    (row column flatIndex : Nat) : ENNReal :=
  if flatIndex = NatProductBijection.encode (row, column) then
    values row column
  else
    zero

private def rowSlice (values : Nat → Nat → ENNReal)
    (row flatIndex : Nat) : ENNReal :=
  if (NatProductBijection.decode flatIndex).1 = row then
    flatten values flatIndex
  else
    zero

private theorem encodedEntryColumnEvaluation
    (values : Nat → Nat → ENNReal) (row column : Nat) :
    tsum (fun flatIndex => encodedEntry values row column flatIndex) =
      values row column := by
  have equal :
      (fun flatIndex => encodedEntry values row column flatIndex) =
        single (NatProductBijection.encode (row, column))
          (values row column) := by
    funext flatIndex
    simp [encodedEntry, single]
  rw [equal, tsumSingle]

private theorem encodedEntryFlatEvaluation
    (values : Nat → Nat → ENNReal) (row flatIndex : Nat) :
    tsum (fun column => encodedEntry values row column flatIndex) =
      rowSlice values row flatIndex := by
  by_cases belongs : (NatProductBijection.decode flatIndex).1 = row
  · have equal :
        (fun column => encodedEntry values row column flatIndex) =
          single (NatProductBijection.decode flatIndex).2
            (flatten values flatIndex) := by
      funext column
      by_cases atIndex :
          column = (NatProductBijection.decode flatIndex).2
      · subst column
        have pairEqual :
            (row, (NatProductBijection.decode flatIndex).2) =
              NatProductBijection.decode flatIndex := by
          apply Prod.ext
          · exact belongs.symm
          · rfl
        have encoded :
            NatProductBijection.encode
                (row, (NatProductBijection.decode flatIndex).2) =
              flatIndex := by
          rw [pairEqual, NatProductBijection.encodeDecode]
        unfold encodedEntry single flatten
        rw [if_pos encoded.symm, if_pos rfl]
        change values row (NatProductBijection.decode flatIndex).2 =
          values (NatProductBijection.decode flatIndex).1
            (NatProductBijection.decode flatIndex).2
        rw [belongs]
      · have notEncoded :
            flatIndex ≠ NatProductBijection.encode (row, column) := by
          intro encoded
          have decodedEqual :
              NatProductBijection.decode flatIndex = (row, column) := by
            rw [encoded, NatProductBijection.decodeEncode]
          have secondEqual :
              (NatProductBijection.decode flatIndex).2 = column :=
            congrArg Prod.snd decodedEqual
          exact atIndex secondEqual.symm
        simp [encodedEntry, single, atIndex, notEncoded]
    rw [equal, tsumSingle]
    simp [rowSlice, belongs]
  · have allZero : ∀ column,
        encodedEntry values row column flatIndex = zero := by
      intro column
      have notEncoded :
          flatIndex ≠ NatProductBijection.encode (row, column) := by
        intro encoded
        apply belongs
        have decodedEqual :
            NatProductBijection.decode flatIndex = (row, column) := by
          rw [encoded, NatProductBijection.decodeEncode]
        exact congrArg Prod.fst decodedEqual
      simp [encodedEntry, notEncoded]
    calc
      tsum (fun column => encodedEntry values row column flatIndex) =
          tsum (fun _ => zero) := tsumCongr allZero
      _ = zero := tsumZero
      _ = rowSlice values row flatIndex := by
        simp [rowSlice, belongs]

private theorem rowSliceEvaluation (values : Nat → Nat → ENNReal)
    (row : Nat) :
    tsum (rowSlice values row) = tsum (values row) := by
  calc
    tsum (rowSlice values row) =
        tsum (fun flatIndex =>
          tsum (fun column =>
            encodedEntry values row column flatIndex)) := by
      apply tsumCongr
      intro flatIndex
      exact (encodedEntryFlatEvaluation values row flatIndex).symm
    _ = tsum (fun column =>
        tsum (fun flatIndex =>
          encodedEntry values row column flatIndex)) :=
      (tsumComm (fun column flatIndex =>
        encodedEntry values row column flatIndex)).symm
    _ = tsum (values row) := by
      apply tsumCongr
      exact encodedEntryColumnEvaluation values row

private theorem rowPartitionEvaluation
    (values : Nat → Nat → ENNReal) (flatIndex : Nat) :
    tsum (fun row => rowSlice values row flatIndex) =
      flatten values flatIndex := by
  have equal :
      (fun row => rowSlice values row flatIndex) =
        single (NatProductBijection.decode flatIndex).1
          (flatten values flatIndex) := by
    funext row
    by_cases atIndex : row = (NatProductBijection.decode flatIndex).1
    · subst row
      simp [rowSlice, single]
    · have reverse :
          (NatProductBijection.decode flatIndex).1 ≠ row :=
        fun equal => atIndex equal.symm
      simp [rowSlice, single, atIndex, reverse]
  rw [equal, tsumSingle]

public theorem tsumFlatten (values : Nat → Nat → ENNReal) :
    tsum (flatten values) = tsum (fun row => tsum (values row)) := by
  calc
    tsum (flatten values) =
        tsum (fun flatIndex =>
          tsum (fun row => rowSlice values row flatIndex)) := by
      apply tsumCongr
      intro flatIndex
      exact (rowPartitionEvaluation values flatIndex).symm
    _ = tsum (fun row => tsum (rowSlice values row)) :=
      (tsumComm (rowSlice values)).symm
    _ = tsum (fun row => tsum (values row)) := by
      apply tsumCongr
      exact rowSliceEvaluation values

end Foundations.Real.ENNReal
