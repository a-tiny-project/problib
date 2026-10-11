module

public import Problib.Analysis.Gaussian.Network.Reverse
public import Problib.Measure.Disintegration.Reconstruction
import Problib.Real.Grind
import Problib.Measure.Measurability.Real

/-! Conditioning a linear-Gaussian network on its first node.

Fixing the first node at `r` substitutes `r` into every later row: row `j`
gains `B_{j0} r` in its intercept and drops its first coefficient
(`instantiateFirst`). The network's density at `r :: t` is the first node's
Gaussian density at `r` times the instantiated network's density at `t`
(`density_cons`).

The conditional law is the explicit kernel `rootKernel`, which sends `r` to the
law of the instantiated network at every `r` (`rootKernel_apply`), so it is a
probability at every `r` and not only almost everywhere. Paired with the first
node's Gaussian marginal it reconstructs the law split into tail and root
(`root_reconstruct`, `root_disintegrates`).

To condition on another node, move it to the front with `reverse_along`
first. Substituting a value into a node's structural equation without that move
fixes the node's noise, not its value, and is not conditioning.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Splitting off and instantiating the first node -/

/-- A list as its tail and its first entry, the root. The root of the empty list
reads as zero. -/
@[expose] public def rootSplit (values : List Carrier) : List Carrier × Carrier :=
  (values.tail, entry values 0)

public theorem rootSplit_measurable :
    MeasurableMap (Space.list borel) (Space.product (Space.list borel) borel) rootSplit :=
  Space.pair_measurable (ListSpace.tail_measurable borel) (entry_measurable 0)

/-- A row with its first parent fixed at `root`. -/
@[expose] public def Row.instantiate (root : Carrier) (row : Row) : Row where
  intercept := add row.intercept (mul (entry row.coefficients 0) root)
  coefficients := row.coefficients.tail
  variance := row.variance

/-- The network of the later nodes with the first node fixed at `root`. -/
@[expose] public def Network.instantiateFirst (network : Network) (root : Carrier) : Network where
  rows := network.rows.tail.map (Row.instantiate root)
  triangular := by
    intro position row found
    rw [List.getElem?_map, List.getElem?_tail] at found
    match original : network.rows[position + 1]?, found with
    | some current, found =>
        cases Option.some.inj found
        simp [Row.instantiate, network.triangular (position + 1) current original]
  positive := by
    intro row member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact network.positive original (List.mem_of_mem_tail inside)

@[simp] public theorem Network.length_instantiateFirst (network : Network) (root : Carrier) :
    (network.instantiateFirst root).length = network.length - 1 := by
  unfold Network.length Network.instantiateFirst
  simp

/-- Peel the first value off, reading a missing first coefficient as zero. -/
public theorem dot_cons_right (coefficients : List Carrier) (root : Carrier)
    (values : List Carrier) :
    dot coefficients (root :: values) =
      add (mul (entry coefficients 0) root) (dot coefficients.tail values) := by
  cases coefficients with
  | nil =>
      change zero = add (mul zero root) (dot [] values)
      rw [dot_nil_left]
      real_grind
  | cons coefficient coefficients => rfl

/-- Reading the instantiated rows at `t` is reading the old rows at `root :: t`. -/
public theorem conditionals_instantiate (rows : List Row) (start : Nat) (root : Carrier)
    (values : List Carrier) :
    conditionals (rows.map (Row.instantiate root)) start values =
      conditionals rows (start + 1) (root :: values) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, conditionals, induction]
      congr 1
      show density (add (add row.intercept (mul (entry row.coefficients 0) root))
          (dot row.coefficients.tail values)) row.variance (entry values start) =
        density (add row.intercept (dot row.coefficients (root :: values))) row.variance
          (entry (root :: values) (start + 1))
      have shifted : entry (root :: values) (start + 1) = entry values start := by
        simp [entry]
      rw [dot_cons_right, shifted]
      congr 1
      real_grind

/-- The instantiated networks' densities, jointly in the root and the tail. -/
@[expose] public def Network.restDensity (network : Network) (pair : Carrier × List Carrier) :
    ENNReal :=
  ENNReal.finite ((network.instantiateFirst pair.1).density pair.2)

public theorem Network.instantiateFirst_density (network : Network) (root : Carrier)
    (values : List Carrier) :
    (network.instantiateFirst root).density values =
      if values.length = network.length - 1 then
        conditionals network.rows.tail 1 (root :: values)
      else NNReal.zero := by
  unfold Network.density
  rw [Network.length_instantiateFirst]
  split
  · exact conditionals_instantiate network.rows.tail 0 root values
  · rfl

public theorem Network.restDensity_measurable (network : Network) :
    ENNRealMeasurable (Space.product borel (Space.list borel)) network.restDensity := by
  have equal : network.restDensity = fun pair =>
      if pair.2.length = network.length - 1 then
        ENNReal.finite (conditionals network.rows.tail 1 (pair.1 :: pair.2))
      else ENNReal.zero := by
    funext pair
    unfold Network.restDensity
    rw [Network.instantiateFirst_density]
    split <;> rfl
  rw [equal]
  apply ENNRealMeasurable.of_measurableMap
  apply MeasurableMap.ite
  · exact Space.second_measurable _ _
      (ListSpace.length_measurable borel (set := fun length => length = network.length - 1) trivial)
  · intro set measurable
    exact ListSpace.cons_measurable borel
      ((conditionals_measurable network.rows.tail 1).measurableMap measurable)
  · exact MeasurableMap.constant _ _ _

/-! ### The root kernel -/

/-- The conditional law of the later nodes given the first: at every root `r`,
the law of the network instantiated at `r`. -/
@[expose] public def Network.rootKernel (network : Network) : Kernel borel (Space.list borel) :=
  Kernel.withDensity (Kernel.const borel (listVolume (network.length - 1)))
    (Kernel.IsSFinite.const borel (listVolumeSFinite (network.length - 1)))
    (fun root values => network.restDensity (root, values)) network.restDensity_measurable

public theorem Network.rootKernel_apply (network : Network) (root : Carrier) :
    network.rootKernel root = (network.instantiateFirst root).law := by
  rw [(network.instantiateFirst root).law_eq_withDensity, Network.length_instantiateFirst]
  rfl

public theorem Network.rootKernel_isProbability (network : Network) (root : Carrier) :
    Measure.IsProbability (network.rootKernel root) := by
  rw [network.rootKernel_apply]
  exact (network.instantiateFirst root).law_isProbability

public def Network.rootKernelSFinite (network : Network) : Kernel.IsSFinite network.rootKernel :=
  (Kernel.IsFinite.of_markov network.rootKernel_isProbability).toSFinite

/-! ### The root marginal and the reconstruction -/

private theorem head_tail_eq (rows : List Row) (nonempty : 0 < rows.length) :
    rows = rows[0] :: rows.tail := by
  cases rows with
  | nil => cases nonempty
  | cons _ _ => rfl

/-- The first row. -/
@[expose] public def Network.root (network : Network) (nonempty : 0 < network.length) : Row :=
  network.rows[0]'nonempty

public theorem Network.root_positive (network : Network) (nonempty : 0 < network.length) :
    lt zero (network.root nonempty).variance :=
  network.positive _ (List.getElem_mem nonempty)

public theorem Network.root_coefficients (network : Network) (nonempty : 0 < network.length) :
    (network.root nonempty).coefficients = [] :=
  List.eq_nil_of_length_eq_zero
    (network.triangular 0 _ (List.getElem?_eq_getElem nonempty))

/-- The first node's law, `N(μ₀, d₀)`. -/
@[expose] public def Network.rootMarginal (network : Network) (nonempty : 0 < network.length) :
    Measure borel :=
  Gaussian.law (network.root nonempty).intercept (network.root nonempty).variance

/-- The first node's Gaussian density at `r`. -/
@[expose] public def Network.rootDensity (network : Network) (nonempty : 0 < network.length)
    (root : Carrier) : ENNReal :=
  ENNReal.finite
    (Gaussian.density (network.root nonempty).intercept (network.root nonempty).variance root)

public theorem Network.rootDensity_positive (network : Network) (nonempty : 0 < network.length)
    (root : Carrier) :
    ENNReal.lt ENNReal.zero (network.rootDensity nonempty root) ∧
      network.rootDensity nonempty root ≠ ENNReal.top :=
  ⟨show ENNReal.lt ENNReal.zero (ENNReal.finite _) from
      density_positive _ _ (network.root_positive nonempty) root,
    ENNReal.finite_ne_top _⟩

/-- The density at `r :: t` is the root density at `r` times the instantiated
network's density at `t`. -/
public theorem Network.density_cons (network : Network) (nonempty : 0 < network.length)
    (root : Carrier) (values : List Carrier) :
    ENNReal.finite (network.density (root :: values)) =
      ENNReal.mul (network.rootDensity nonempty root) (network.restDensity (root, values)) := by
  have empty := network.root_coefficients nonempty
  have rowsEq : network.rows = network.root nonempty :: network.rows.tail :=
    head_tail_eq network.rows nonempty
  unfold Network.restDensity Network.rootDensity
  rw [Network.instantiateFirst_density]
  unfold Network.density
  by_cases counted : values.length = network.length - 1
  · rw [ite_eq_left (show (root :: values).length = network.length by
      simp only [List.length_cons]; omega), ite_eq_left counted, ENNReal.finite_mul_finite]
    congr 1
    rw [rowsEq]
    simp only [conditionals, List.tail_cons]
    congr 1
    unfold Row.density Row.mean
    rw [empty, dot_nil_left, add_zero]
    rfl
  · rw [ite_eq_right (show ¬(root :: values).length = network.length by
      simp only [List.length_cons]; omega), ite_eq_right counted, ENNReal.finite_mul_finite,
      NNReal.mul_zero]

/-- The law split into tail and root is the root marginal followed by the root
kernel. -/
public theorem Network.root_reconstruct (network : Network) (nonempty : 0 < network.length) :
    network.law.map rootSplit rootSplit_measurable =
      Measure.reverseSemiproduct (network.rootMarginal nonempty) network.rootKernel
        network.rootKernelSFinite := by
  obtain ⟨count, counted⟩ : ∃ count, network.length = count + 1 :=
    ⟨network.length - 1, by omega⟩
  have joint : (network.rootMarginal nonempty).semiproduct network.rootKernel
      network.rootKernelSFinite =
      (Measure.prod volume (listVolume (network.length - 1))
        (listVolumeSFinite (network.length - 1))).withDensity
        (fun pair => ENNReal.mul (network.restDensity pair)
          (network.rootDensity nonempty pair.1)) := by
    unfold Network.rootMarginal
    rw [Gaussian.law_eq_withDensity _ _ (network.root_positive nonempty)]
    exact Measure.semiproduct_withDensity_prod volume
      (density_measurable_slice (network.root nonempty).intercept (network.root nonempty).variance)
      (listVolume _) (listVolumeSFinite _) network.rootKernel network.rootKernelSFinite
      network.restDensity_measurable (fun _ => rfl)
  have volumeForm : listVolume network.length =
      (Measure.prod volume (listVolume (network.length - 1))
        (listVolumeSFinite (network.length - 1))).map (fun input => input.1 :: input.2)
        (ListSpace.cons_measurable borel) := by
    rw [counted, Nat.add_sub_cancel]
    rfl
  unfold Measure.reverseSemiproduct
  rw [joint, network.law_eq_withDensity, volumeForm,
    ← Measure.map_withDensity _ _ (ListSpace.cons_measurable borel) network.density_measurable,
    Measure.map_comp,
    Measure.map_congr_function _ _ (Space.swap_measurable _ _) (funext fun _ => rfl)]
  congr 1
  congr 1
  funext pair
  rw [network.density_cons nonempty, ENNReal.mul_comm]

/-- The root kernel disintegrates the law split into tail and root. -/
public theorem Network.root_disintegrates (network : Network) (nonempty : 0 < network.length) :
    Measure.Disintegrates (network.law.map rootSplit rootSplit_measurable) network.rootKernel
      network.rootKernelSFinite := by
  have marginal : Measure.secondMarginal (network.law.map rootSplit rootSplit_measurable) =
      network.rootMarginal nonempty := by
    rw [network.root_reconstruct nonempty]
    unfold Measure.secondMarginal Measure.reverseSemiproduct
    rw [Measure.map_comp]
    exact semiproduct_map_first _ _ _ network.rootKernel_isProbability
  unfold Measure.Disintegrates
  rw [marginal]
  exact (network.root_reconstruct nonempty).symm

end
end Problib.Analysis.Gaussian
