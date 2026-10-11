import Problib.Linear.Rational.Sum

namespace Problib.Linear.Rational

abbrev Vector (dimension : Nat) := Fin dimension → Rat

abbrev Matrix (rows columns : Nat) := Fin rows → Fin columns → Rat

namespace Vector

def zero (dimension : Nat) : Vector dimension :=
  fun _ => 0

@[reducible] def basis {dimension : Nat} (coordinate : Fin dimension) : Vector dimension :=
  fun index => if index = coordinate then 1 else 0

def add {dimension : Nat} (left right : Vector dimension) : Vector dimension :=
  fun index => left index + right index

def scale {dimension : Nat} (constant : Rat) (vector : Vector dimension) :
    Vector dimension :=
  fun index => constant * vector index

def dot {dimension : Nat} (left right : Vector dimension) : Rat :=
  finSum fun index => left index * right index

@[ext] theorem ext {dimension : Nat} {left right : Vector dimension}
    (equal : ∀ index, left index = right index) : left = right :=
  funext equal

end Vector

namespace Matrix

@[reducible] def zero (rows columns : Nat) : Matrix rows columns :=
  fun _ _ => 0

@[reducible] def apply {rows columns : Nat} (matrix : Matrix rows columns)
    (vector : Vector columns) : Vector rows :=
  fun row => finSum fun column => matrix row column * vector column

@[reducible] def transpose {rows columns : Nat} (matrix : Matrix rows columns) : Matrix columns rows :=
  fun column row => matrix row column

@[reducible] def transposeApply {rows columns : Nat} (matrix : Matrix rows columns)
    (cotangent : Vector rows) : Vector columns :=
  apply (transpose matrix) cotangent

@[ext] theorem ext {rows columns : Nat} {left right : Matrix rows columns}
    (equal : ∀ row column, left row column = right row column) : left = right := by
  apply funext
  intro row
  exact funext (equal row)

@[simp] theorem transpose_involution {rows columns : Nat} (matrix : Matrix rows columns) :
    transpose (transpose matrix) = matrix := by
  ext row column
  rfl

theorem apply_basis {rows columns : Nat} (matrix : Matrix rows columns)
    (column : Fin columns) (row : Fin rows) :
    apply matrix (Vector.basis column) row = matrix row column := by
  unfold apply Vector.basis
  calc
    finSum (fun index => matrix row index * if index = column then 1 else 0) =
        finSum (fun index => if index = column then matrix row index else 0) := by
          apply finSum_congr
          intro index
          by_cases equal : index = column <;> simp [equal]
    _ = matrix row column := finSum_indicator column fun index => matrix row index

theorem apply_add {rows columns : Nat} (matrix : Matrix rows columns)
    (left right : Vector columns) :
    apply matrix (Vector.add left right) =
      Vector.add (apply matrix left) (apply matrix right) := by
  apply Vector.ext
  intro row
  calc
    finSum (fun column => matrix row column * (left column + right column)) =
        finSum (fun column =>
          matrix row column * left column + matrix row column * right column) := by
            apply finSum_congr
            intro column
            exact Rat.mul_add _ _ _
    _ = finSum (fun column => matrix row column * left column) +
        finSum (fun column => matrix row column * right column) :=
      finSum_add _ _

theorem apply_scale {rows columns : Nat} (matrix : Matrix rows columns)
    (constant : Rat) (vector : Vector columns) :
    apply matrix (Vector.scale constant vector) =
      Vector.scale constant (apply matrix vector) := by
  apply Vector.ext
  intro row
  calc
    finSum (fun column => matrix row column * (constant * vector column)) =
        finSum (fun column => constant * (matrix row column * vector column)) := by
          apply finSum_congr
          intro column
          calc
            matrix row column * (constant * vector column) =
                (matrix row column * constant) * vector column :=
              (Rat.mul_assoc _ _ _).symm
            _ = (constant * matrix row column) * vector column := by
              rw [Rat.mul_comm (matrix row column) constant]
            _ = constant * (matrix row column * vector column) :=
              Rat.mul_assoc _ _ _
    _ = constant * finSum (fun column => matrix row column * vector column) :=
      finSum_scale_left constant _

theorem transpose_adjoint {rows columns : Nat} (matrix : Matrix rows columns)
    (tangent : Vector columns) (cotangent : Vector rows) :
    Vector.dot (apply matrix tangent) cotangent =
      Vector.dot tangent (transposeApply matrix cotangent) := by
  calc
    Vector.dot (apply matrix tangent) cotangent =
        finSum (fun row =>
          finSum (fun column => matrix row column * tangent column) * cotangent row) := rfl
    _ = finSum (fun row => finSum fun column =>
        (matrix row column * tangent column) * cotangent row) := by
          apply finSum_congr
          intro row
          exact (finSum_scale_right
            (fun column => matrix row column * tangent column) (cotangent row)).symm
    _ = finSum (fun column => finSum fun row =>
        (matrix row column * tangent column) * cotangent row) :=
      finSum_swap fun row column => (matrix row column * tangent column) * cotangent row
    _ = finSum (fun column => finSum fun row =>
        tangent column * (matrix row column * cotangent row)) := by
          apply finSum_congr
          intro column
          apply finSum_congr
          intro row
          calc
            (matrix row column * tangent column) * cotangent row =
                (tangent column * matrix row column) * cotangent row := by
              rw [Rat.mul_comm (matrix row column) (tangent column)]
            _ = tangent column * (matrix row column * cotangent row) :=
              Rat.mul_assoc _ _ _
    _ = finSum (fun column =>
        tangent column * finSum (fun row => matrix row column * cotangent row)) := by
          apply finSum_congr
          intro column
          exact finSum_scale_left (tangent column)
            (fun row => matrix row column * cotangent row)
    _ = Vector.dot tangent (transposeApply matrix cotangent) := rfl

end Matrix

end Problib.Linear.Rational
