module

public import Problib.Analysis.Gaussian.Network.Law
public import Problib.Analysis.Gaussian.Curve
import Problib.Real.Grind

/-! The log density of a linear-Gaussian network.

A network's density is the product of its scalar conditionals, so its logarithm
is a sum over the nodes. Node `i` contributes its squared residual
`rᵢ = xᵢ − μᵢ − ⟨Bᵢ, x₍<ᵢ₎⟩` over its innovation variance, and half the
logarithm of `2π dᵢ`:

  `log p(x) = −logNormalizer − ½ Σᵢ rᵢ² / dᵢ`,
  `logNormalizer = ½ Σᵢ (log 2π + log dᵢ) = ½ (n log 2π + Σᵢ log dᵢ)`.

The normalizer is named for what it is. It is not called a log determinant,
because nothing here relates `Σᵢ log dᵢ` to a determinant. Neither term alone
scores a point: two networks can share `Σᵢ log dᵢ` and still score `x`
differently, so a delivered log density carries both terms and the dimension
constant.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Logarithm (logIntegral log_mul log_one)

noncomputable section

namespace Network

/-- The residual of node `i` at `x`: `xᵢ − μᵢ − ⟨Bᵢ, x₍<ᵢ₎⟩`, and zero past the
last node. -/
@[expose] public def residual (network : Network) (values : List Carrier) (index : Nat) :
    Carrier :=
  match network.rows[index]? with
  | some row => sub (entry values index) (row.mean values)
  | none => zero

/-- `½ Σᵢ (log 2π + log dᵢ)`, which is `½ (n log 2π + Σᵢ log dᵢ)`. -/
@[expose] public def logNormalizer (network : Network) : Carrier :=
  div (sumBelow network.length fun index =>
      add (logIntegral (mul (selection.ofRat 2) pi)) (logIntegral (entry network.variance index)))
    (selection.ofRat 2)

end Network

/-! ### The product of the conditionals -/

/-- A product of conditionals with positive variances is positive. -/
public theorem conditionals_positive (rows : List Row)
    (positive : ∀ row ∈ rows, lt zero row.variance) (start : Nat) (values : List Carrier) :
    lt zero (conditionals rows start values).toReal := by
  induction rows generalizing start with
  | nil => exact one_positive
  | cons row rows induction =>
      change lt zero (mul (row.density values start).toReal (conditionals rows (start + 1) values).toReal)
      exact mul_positive (density_positive _ _ (positive row (List.mem_cons_self ..)) _)
        (induction (fun other member => positive other (List.mem_cons_of_mem _ member)) _)

/-- The logarithm of a product of conditionals is the sum of the scalar log
densities. -/
public theorem log_conditionals (rows : List Row)
    (positive : ∀ row ∈ rows, lt zero row.variance) (start : Nat) (values : List Carrier) :
    logIntegral (conditionals rows start values).toReal =
      sumBelow rows.length fun index =>
        match rows[index]? with
        | some row => logDensity (row.mean values) row.variance (entry values (start + index))
        | none => zero := by
  induction rows generalizing start with
  | nil => exact log_one
  | cons row rows induction =>
      have rowPositive := positive row (List.mem_cons_self ..)
      have restPositive : ∀ other ∈ rows, lt zero other.variance :=
        fun other member => positive other (List.mem_cons_of_mem _ member)
      change logIntegral (mul (row.density values start).toReal
        (conditionals rows (start + 1) values).toReal) = _
      rw [log_mul (row.density values start).toReal _ (density_positive _ _ rowPositive _)
          (conditionals_positive rows restPositive _ _),
        induction restPositive, List.length_cons, sumBelow_succ_left]
      unfold Row.density
      rw [density_exp _ _ _ rowPositive, Problib.Analysis.log_exp]
      congr 1
      apply sumBelow_congr
      intro index _
      simp only [List.getElem?_cons_succ]
      rw [show start + 1 + index = start + (index + 1) by omega]

/-! ### The log density -/

/-- Halves of two sums, collected. -/
public theorem sumBelow_halves (count : Nat) (square constant : Nat → Carrier) :
    sumBelow count (fun index => sub (neg (div (square index) (selection.ofRat 2)))
        (div (constant index) (selection.ofRat 2))) =
      sub (neg (div (sumBelow count constant) (selection.ofRat 2)))
        (div (sumBelow count square) (selection.ofRat 2)) := by
  induction count with
  | zero =>
      change zero = sub (neg (div zero _)) (div zero _)
      real_grind
  | succ count induction =>
      change add (sumBelow count _) _ =
        sub (neg (div (add (sumBelow count constant) (constant count)) _))
          (div (add (sumBelow count square) (square count)) _)
      rw [induction]
      real_grind

/-- The scalar log density at a node, in the network's terms. -/
private theorem logDensity_node {network : Network} {index : Nat} {row : Row}
    (found : network.rows[index]? = some row) (values : List Carrier) :
    logDensity (row.mean values) row.variance (entry values index) =
      sub (neg (div (div (mul (network.residual values index) (network.residual values index))
          (entry network.variance index)) (selection.ofRat 2)))
        (div (add (logIntegral (mul (selection.ofRat 2) pi))
          (logIntegral (entry network.variance index))) (selection.ofRat 2)) := by
  have variance : entry network.variance index = row.variance := by
    simp [entry, Network.variance, List.getD_eq_getElem?_getD, found]
  have rowPositive : lt zero row.variance :=
    network.positive row (List.mem_of_getElem? found)
  have residual : network.residual values index = sub (entry values index) (row.mean values) := by
    unfold Network.residual
    rw [found]
  rw [variance, residual, ← log_mul _ _ (mul_positive ofRat_two_positive pi_positive) rowPositive]
  unfold logDensity
  have nonzero : row.variance ≠ zero := fun vanished => by
    rw [vanished] at rowPositive
    exact lt_irrefl _ rowPositive
  real_grind

/-- The log density of a network at a list of its length: minus the
normalizer, minus half the sum of squared residuals over innovation variances. -/
public theorem Network.log_density (network : Network) (values : List Carrier)
    (length : values.length = network.length) :
    logIntegral (network.density values).toReal =
      sub (neg network.logNormalizer)
        (div (sumBelow network.length fun index =>
            div (mul (network.residual values index) (network.residual values index))
              (entry network.variance index))
          (selection.ofRat 2)) := by
  unfold Network.density
  rw [ite_eq_left length, log_conditionals network.rows network.positive 0 values,
    Network.logNormalizer, ← sumBelow_halves]
  apply sumBelow_congr
  intro index below
  have found : network.rows[index]? = some network.rows[index] :=
    List.getElem?_eq_getElem below
  simp only [found, Nat.zero_add]
  exact logDensity_node found values

/-- At a list of its length, a network's density is positive. -/
public theorem Network.density_positive (network : Network) (values : List Carrier)
    (length : values.length = network.length) :
    lt zero (network.density values).toReal := by
  unfold Network.density
  rw [ite_eq_left length]
  exact conditionals_positive network.rows network.positive 0 values

end

end Problib.Analysis.Gaussian
