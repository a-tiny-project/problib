module

public import Problib.Measure.Real.Interval

/-! Linear-Gaussian networks in a fixed order, and their moment recurrences.

A network draws its nodes in order. Node `i` is Gaussian with mean
`μᵢ + Σ_{j<i} Bᵢⱼ xⱼ` and variance `dᵢ > 0`, so it is a linear regression on
the earlier nodes plus independent noise. This is the factorization `LDLᵀ` of
a covariance read as a program: no matrix inverse, determinant or Jacobian is
needed to state its law, its density or its moves.

A network is one list of rows. Row `i` carries the intercept `μᵢ`, exactly `i`
coefficients (`Triangular`) and a positive innovation variance. The intercept
is not the marginal mean in general. The marginal mean and covariance are the
recurrences `meanAppend` and `covarianceAppend` folded over the rows. In closed
form they are `A⁻¹μ` and `A⁻¹DA⁻ᵀ` with `A = I − B`, but nothing here states
the closed form.

Positions are rearranged by adjacent swaps (`swapAt`). A permutation is given
as the word of adjacent swaps that realizes it (`permute`).
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

universe u

/-! ### Rows and networks -/

/-- One node: its intercept, its regression on the earlier nodes, and its
innovation variance. -/
public structure Row where
  intercept : Carrier
  coefficients : List Carrier
  variance : Carrier

/-- Row `i` has exactly `i` coefficients, one for each earlier node. -/
@[expose] public def Triangular (rows : List Row) : Prop :=
  ∀ (index : Nat) (row : Row), rows[index]? = some row → row.coefficients.length = index

/-- A linear-Gaussian network: triangular rows with positive innovation variances. -/
public structure Network where
  rows : List Row
  triangular : Triangular rows
  positive : ∀ row ∈ rows, lt zero row.variance

/-- The sum `Σ bⱼ xⱼ` over the shorter of the two lists. -/
@[expose] public def dot : List Carrier → List Carrier → Carrier
  | coefficient :: coefficients, value :: values =>
      add (mul coefficient value) (dot coefficients values)
  | _, _ => zero

namespace Network

/-- The number of nodes. -/
@[expose] public def length (network : Network) : Nat := network.rows.length

/-- The intercepts `μ`. -/
@[expose] public def intercept (network : Network) : List Carrier :=
  network.rows.map Row.intercept

/-- The coefficient rows `B`, row `i` with `i` entries. -/
@[expose] public def coefficients (network : Network) : List (List Carrier) :=
  network.rows.map Row.coefficients

/-- The innovation variances `d`. -/
@[expose] public def variance (network : Network) : List Carrier :=
  network.rows.map Row.variance

public theorem ext {left right : Network} (rows : left.rows = right.rows) : left = right := by
  cases left
  cases right
  cases rows
  rfl

end Network

/-! ### Construction from three lists -/

/-- Three lists of equal length, with row `i` of `B` holding `i` entries. -/
@[expose] public def Shaped (intercept : List Carrier) (coefficients : List (List Carrier))
    (variance : List Carrier) : Prop :=
  intercept.length = coefficients.length ∧ variance.length = coefficients.length ∧
    ∀ (index : Nat) (row : List Carrier), coefficients[index]? = some row → row.length = index

/-- Zip three lists into rows. -/
@[expose] public def rowsOf : List Carrier → List (List Carrier) → List Carrier → List Row
  | intercept :: intercepts, row :: rows, variance :: variances =>
      ⟨intercept, row, variance⟩ :: rowsOf intercepts rows variances
  | _, _, _ => []

public theorem rowsOf_getElem? (intercepts : List Carrier) (rows : List (List Carrier))
    (variances : List Carrier) (index : Nat) (row : Row)
    (found : (rowsOf intercepts rows variances)[index]? = some row) :
    rows[index]? = some row.coefficients ∧ variances[index]? = some row.variance := by
  induction rows generalizing intercepts variances index with
  | nil => cases intercepts <;> cases variances <;> simp [rowsOf] at found
  | cons head tail induction =>
      cases intercepts with
      | nil => simp [rowsOf] at found
      | cons intercept intercepts =>
          cases variances with
          | nil => simp [rowsOf] at found
          | cons variance variances =>
              cases index with
              | zero =>
                  simp only [rowsOf, List.getElem?_cons_zero, Option.some.injEq] at found
                  subst found
                  exact ⟨rfl, rfl⟩
              | succ index =>
                  simp only [rowsOf, List.getElem?_cons_succ] at found
                  simpa only [List.getElem?_cons_succ] using
                    induction intercepts variances index found

private theorem rowsOf_map (intercepts : List Carrier) (rows : List (List Carrier))
    (variances : List Carrier) (interceptLength : intercepts.length = rows.length)
    (varianceLength : variances.length = rows.length) :
    (rowsOf intercepts rows variances).map Row.intercept = intercepts ∧
      (rowsOf intercepts rows variances).map Row.coefficients = rows ∧
      (rowsOf intercepts rows variances).map Row.variance = variances := by
  induction rows generalizing intercepts variances with
  | nil =>
      rw [List.length_eq_zero_iff.mp interceptLength, List.length_eq_zero_iff.mp varianceLength]
      exact ⟨rfl, rfl, rfl⟩
  | cons head tail induction =>
      cases intercepts with
      | nil => cases interceptLength
      | cons intercept intercepts =>
          cases variances with
          | nil => cases varianceLength
          | cons variance variances =>
              have next := induction intercepts variances (Nat.succ.inj interceptLength)
                (Nat.succ.inj varianceLength)
              simp only [rowsOf, List.map_cons]
              exact ⟨congrArg _ next.1, congrArg _ next.2.1, congrArg _ next.2.2⟩

/-- The network with intercepts `μ`, coefficient rows `B` and variances `d`. -/
@[expose] public def Network.ofLists (intercept : List Carrier) (coefficients : List (List Carrier))
    (variance : List Carrier) (shaped : Shaped intercept coefficients variance)
    (positive : ∀ value ∈ variance, lt zero value) : Network where
  rows := rowsOf intercept coefficients variance
  triangular index row found :=
    shaped.2.2 index row.coefficients (rowsOf_getElem? _ _ _ index row found).1
  positive row member := by
    obtain ⟨index, found⟩ := List.getElem?_of_mem member
    exact positive row.variance
      (List.mem_of_getElem? (rowsOf_getElem? _ _ _ index row found).2)

public theorem Network.ofLists_intercept (intercept coefficients variance shaped positive) :
    (Network.ofLists intercept coefficients variance shaped positive).intercept = intercept :=
  (rowsOf_map intercept coefficients variance shaped.1 shaped.2.1).1

public theorem Network.ofLists_coefficients (intercept coefficients variance shaped positive) :
    (Network.ofLists intercept coefficients variance shaped positive).coefficients =
      coefficients :=
  (rowsOf_map intercept coefficients variance shaped.1 shaped.2.1).2.1

public theorem Network.ofLists_variance (intercept coefficients variance shaped positive) :
    (Network.ofLists intercept coefficients variance shaped positive).variance = variance :=
  (rowsOf_map intercept coefficients variance shaped.1 shaped.2.1).2.2

/-! ### Appending and dropping the last node -/

namespace Network

/-- Append a node whose regression covers every existing node. -/
@[expose] public def append (network : Network) (row : Row)
    (shaped : row.coefficients.length = network.length) (positive : lt zero row.variance) :
    Network where
  rows := network.rows ++ [row]
  triangular index current found := by
    rcases Nat.lt_or_ge index network.rows.length with below | above
    · rw [List.getElem?_append_left below] at found
      exact network.triangular index current found
    · rw [List.getElem?_append_right above] at found
      rcases Nat.lt_or_ge (index - network.rows.length) 1 with first | beyond
      · have equal : index = network.rows.length := by omega
        rw [equal, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        rw [equal]
        exact shaped
      · rw [List.getElem?_eq_none (by simpa using beyond)] at found
        cases found
  positive current member := by
    rcases List.mem_append.mp member with old | new
    · exact network.positive current old
    · rw [List.mem_singleton.mp new]
      exact positive

/-- Drop the last node. -/
@[expose] public def init (network : Network) : Network where
  rows := network.rows.dropLast
  triangular index row found := by
    apply network.triangular index row
    rw [List.getElem?_dropLast] at found
    split at found
    · exact found
    · cases found
  positive row member := network.positive row (List.dropLast_subset _ member)

@[simp] public theorem length_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).length = network.length + 1 := by
  simp [append, length]

@[simp] public theorem length_init (network : Network) :
    network.init.length = network.length - 1 := by
  simp [init, length]

/-- Appending a node and dropping it again returns the network. -/
@[simp] public theorem init_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).init = network :=
  ext List.dropLast_concat

/-- A nonempty network is its initial part with its last row appended. -/
public theorem append_init_last (network : Network) (nonempty : network.rows ≠ []) :
    ∃ shaped positive,
      network.init.append (network.rows.getLast nonempty) shaped positive = network := by
  have last := network.rows.getLast_mem nonempty
  refine ⟨?_, network.positive _ last, ext (List.dropLast_concat_getLast nonempty)⟩
  apply network.triangular
  rw [length_init, length, List.getLast_eq_getElem]
  have positive : 0 < network.rows.length := List.length_pos_iff.mpr nonempty
  simp [List.getElem?_eq_getElem (by omega : network.rows.length - 1 < network.rows.length)]

/-- Induction from the empty network by appending one node at a time. -/
public theorem induction {motive : Network → Prop}
    (empty : ∀ network : Network, network.rows = [] → motive network)
    (append : ∀ (network : Network) (row : Row) (shaped positive),
      motive network → motive (network.append row shaped positive))
    (network : Network) : motive network := by
  generalize counted : network.rows.length = count
  induction count generalizing network with
  | zero => exact empty network (List.length_eq_zero_iff.mp counted)
  | succ count induction =>
      have nonempty : network.rows ≠ [] := by
        intro vanished
        rw [vanished] at counted
        cases counted
      obtain ⟨shaped, positive, rebuilt⟩ := network.append_init_last nonempty
      rw [← rebuilt]
      apply append
      apply induction
      change network.rows.dropLast.length = count
      rw [List.length_dropLast, counted]
      rfl

end Network

/-! ### The mean and covariance recurrences -/

/-- The mean after appending `row`: `mᵢ = μᵢ + ⟨b, m⟩`. -/
@[expose] public def meanAppend (mean : List Carrier) (row : Row) : List Carrier :=
  mean ++ [add row.intercept (dot row.coefficients mean)]

/-- The covariance after appending `row` with coefficients `b` and variance
`d`: `[[Σ, Σb], [bᵀΣ, bᵀΣb + d]]`. Each matrix is its list of rows. -/
@[expose] public def covarianceAppend (covariance : List (List Carrier)) (row : Row) :
    List (List Carrier) :=
  let cross := covariance.map (fun current => dot current row.coefficients)
  covariance.map (fun current => current ++ [dot current row.coefficients]) ++
    [cross ++ [add (dot row.coefficients cross) row.variance]]

namespace Network

/-- The marginal mean, by the recurrence. -/
@[expose] public def mean (network : Network) : List Carrier :=
  network.rows.foldl meanAppend []

/-- The marginal covariance, by the recurrence. -/
@[expose] public def covariance (network : Network) : List (List Carrier) :=
  network.rows.foldl covarianceAppend []

public theorem mean_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).mean = meanAppend network.mean row := by
  simp [mean, append, List.foldl_append]

public theorem covariance_append (network : Network) (row : Row) (shaped positive) :
    (network.append row shaped positive).covariance =
      covarianceAppend network.covariance row := by
  simp [covariance, append, List.foldl_append]

end Network

/-! ### Adjacent swaps and permutations -/

section Swap

variable {α : Type u}

/-- Exchange positions `i` and `i + 1`. A list too short for both is unchanged. -/
@[expose] public def swapAt : Nat → List α → List α
  | 0, first :: second :: rest => second :: first :: rest
  | index + 1, first :: rest => first :: swapAt index rest
  | _, values => values

@[simp] public theorem swapAt_length (index : Nat) (values : List α) :
    (swapAt index values).length = values.length := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons first rest induction =>
      cases index with
      | zero => cases rest <;> rfl
      | succ index => simp [swapAt, induction]

@[simp] public theorem swapAt_swapAt (index : Nat) (values : List α) :
    swapAt index (swapAt index values) = values := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons first rest induction =>
      cases index with
      | zero => cases rest <;> rfl
      | succ index => simp [swapAt, induction]

/-- The swap leaves a list unchanged when position `i + 1` does not exist. -/
public theorem swapAt_of_le {index : Nat} {values : List α} (short : values.length ≤ index + 1) :
    swapAt index values = values := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons first rest induction =>
      cases index with
      | zero =>
          cases rest with
          | nil => rfl
          | cons second rest => simp at short
      | succ index =>
          simp only [swapAt, List.cons.injEq, true_and]
          exact induction (by simpa using short)

/-- Apply a word of adjacent swaps from left to right. Every permutation of a
finite list is such a word. -/
@[expose] public def permute (word : List Nat) (values : List α) : List α :=
  word.foldl (fun current index => swapAt index current) values

@[simp] public theorem permute_nil (values : List α) : permute [] values = values := rfl

@[simp] public theorem permute_cons (index : Nat) (word : List Nat) (values : List α) :
    permute (index :: word) values = permute word (swapAt index values) := rfl

@[simp] public theorem permute_length (word : List Nat) (values : List α) :
    (permute word values).length = values.length := by
  induction word generalizing values with
  | nil => rfl
  | cons index word induction => simp [induction]

/-- Swap rows `i` and `i + 1` and columns `i` and `i + 1` of a square matrix. -/
@[expose] public def swapMatrixAt (index : Nat) (matrix : List (List α)) : List (List α) :=
  swapAt index (matrix.map (swapAt index))

end Swap

end
end Problib.Analysis.Gaussian
