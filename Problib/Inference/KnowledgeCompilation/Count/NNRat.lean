import Problib.Inference.KnowledgeCompilation.Count
import Problib.Probability.NNRat

namespace Problib.Inference.KnowledgeCompilation

open Problib.Probability

/-- With one omitted Boolean input, on-path counting gives one but exact counting gives two. -/
theorem countOmitting_necessary :
    ∃ (diagram : Diagram) (order : List Nat) (weights : Weights NNRat),
      diagram.Valid order ∧
      diagram.countOmitting NNRat.semiring weights (fun _ => 1) 1 ≠
        diagram.countAt NNRat.semiring order weights (fun _ => 1) 1 := by
  apply countOmitting_necessary_of_nonidempotent NNRat.semiring
  intro equal
  have rational := congrArg NNRat.val equal
  simp [NNRat.semiring, NNRat.val_add, NNRat.val_one] at rational
  have two : (1 : Rat) + 1 = 2 := (Rat.natCast_add 1 1).symm
  rw [two] at rational
  exact (by decide : (2 : Rat) ≠ 1) rational

end Problib.Inference.KnowledgeCompilation
