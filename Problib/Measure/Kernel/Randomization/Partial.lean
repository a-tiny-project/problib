module

public import Problib.Measure.Kernel.Randomization.Unit
public import Problib.Measure.Kernel.Scale
public import Problib.Measure.Additive.Comap
public import Problib.Measure.Embedding.Sum
public import Problib.Measure.StandardBorel.Real
public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.Scale
public import Problib.Measure.Uniform
public import Problib.Real.Grind

/-!
# Partial Lebesgue randomization of s-finite kernels

A probability kernel is the law of a jointly measurable function of its input
and one uniform seed. This module extends that to s-finite kernels, whose fibres
may have infinite mass, by changing two things. The seed ranges over the whole
real line under Lebesgue volume, which has infinite mass. The function may fail,
and only the volume of seeds that do not fail counts.

The construction splits the kernel into its bounded components. It scales the
`index`th component by the inverse of a width that exceeds its bound, and pads
the result to a probability kernel with a failure code. The uniform randomizer
of that padded kernel runs on a strip of the line of exactly that width, so the
strip returns the component's mass. The strips are disjoint, and seeds outside
every strip fail. Zero kernels and an empty target need no chosen point: their
padded kernels put all mass on the failure code.

Not claimed: the converse, that a partially randomized kernel is s-finite.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real
open Problib.Real.Construction
open Problib.Measure.Real

universe u v

public section

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- A jointly measurable partial map from an input and a real seed into the
target. Lebesgue volume pushed through it at each input, read on the target
summand, is the kernel's fibre. -/
structure PartialRandomizer (kernel : Kernel source target) where
  function : alpha × Carrier → Sum Unit beta
  measurable : MeasurableMap (Space.product source borel)
    (Space.sum (Space.discrete Unit) target) function
  law : ∀ input, (volume.map (fun seed => function (input, seed))
      (MeasurableMap.comp measurable (Space.pair_measurable
        (MeasurableMap.constant borel source input) (MeasurableMap.identity borel)))).comap
      (MeasurableEmbedding.inr (Space.discrete Unit) target) = kernel input

namespace PartialRandomizer

/-! ### Strips of the real line -/

/-- The coordinate that places the strip `(shift, shift + width]` on `(0, 1]`. -/
@[expose] noncomputable def stripCoordinate (shift width value : Carrier) : Carrier :=
  Dedekind.mul (Dedekind.inverse width) (Dedekind.add (Dedekind.neg shift) value)

theorem stripCoordinate_measurable (shift width : Carrier) :
    MeasurableMap borel borel (stripCoordinate shift width) :=
  MeasurableMap.comp (scale_measurable_any (Dedekind.inverse width))
    (translate_measurable (Dedekind.neg shift))

theorem stripCoordinate_affine (shift : Carrier) {width : Carrier}
    (positive : Dedekind.lt Dedekind.zero width) (value : Carrier) :
    stripCoordinate shift width (Dedekind.add shift (Dedekind.mul width value)) = value := by
  have nonzero : width ≠ Dedekind.zero := fun equal =>
    positive.2 (by rw [equal]; exact Dedekind.le_refl _)
  unfold stripCoordinate
  real_grind

/-- The strip `(shift, shift + width]`, read through its coordinate. -/
@[expose] def strip (shift width : Carrier) : Set Carrier :=
  Set.preimage (stripCoordinate shift width) (Ioc Dedekind.zero Dedekind.one)

theorem strip_measurable (shift width : Carrier) : borel.Measurable (strip shift width) :=
  stripCoordinate_measurable shift width (measurable_ioc _ _)

theorem strip_bounds {shift width value : Carrier}
    (positive : Dedekind.lt Dedekind.zero width) (member : strip shift width value) :
    Dedekind.lt shift value ∧ Dedekind.le value (Dedekind.add shift width) := by
  have restored : value = Dedekind.add shift
      (Dedekind.mul width (stripCoordinate shift width value)) := by
    have nonzero : width ≠ Dedekind.zero := fun equal =>
      positive.2 (by rw [equal]; exact Dedekind.le_refl _)
    unfold stripCoordinate
    real_grind
  have lower := Dedekind.mul_lt_mul_positive_left member.1 positive
  have upper := Dedekind.mul_le_mul_nonnegative_left member.2 positive.1
  rw [restored]
  constructor <;> real_grind

/-- The unit coordinate of a seed, clamped into the unit interval. -/
@[expose] noncomputable def stripSeed (shift width value : Carrier) : UnitInterval :=
  clamp01 (stripCoordinate shift width value)

theorem stripSeed_measurable (shift width : Carrier) :
    MeasurableMap borel unitBorel (stripSeed shift width) :=
  MeasurableMap.comp clamp01_measurable (stripCoordinate_measurable shift width)

/-- The strip equation: Lebesgue volume on a strip of positive width, read
through its unit coordinate, is the width times the uniform law. -/
theorem volume_strip (shift : Carrier) {width : Carrier}
    (positive : Dedekind.lt Dedekind.zero width)
    {region : Set UnitInterval} (measurable : unitBorel.Measurable region) :
    volume (Set.inter (strip shift width) (Set.preimage (stripSeed shift width) region)) =
      ENNReal.mul (ENNReal.ofReal width) (uniform01 region) := by
  let inside := Set.inter (strip shift width) (Set.preimage (stripSeed shift width) region)
  have insideMeasurable : borel.Measurable inside :=
    borel.inter (strip_measurable shift width) (stripSeed_measurable shift width measurable)
  have pulled : Set.preimage (fun value => Dedekind.add shift (Dedekind.mul width value))
      inside = Set.inter (Ioc Dedekind.zero Dedekind.one) (Set.preimage clamp01 region) := by
    apply Set.ext
    intro value
    change (Ioc Dedekind.zero Dedekind.one
        (stripCoordinate shift width (Dedekind.add shift (Dedekind.mul width value))) ∧
      region (clamp01
        (stripCoordinate shift width (Dedekind.add shift (Dedekind.mul width value))))) ↔ _
    rw [stripCoordinate_affine shift positive]
    exact Iff.rfl
  have scaled := congrArg (fun measure : Measure borel => measure inside)
    (map_volume_affine shift width positive)
  rw [Measure.map_apply _ _ _ insideMeasurable, pulled,
    Measure.smul_apply_measurable _ _ insideMeasurable] at scaled
  have unit : volume (Set.inter (Ioc Dedekind.zero Dedekind.one) (Set.preimage clamp01 region)) =
      uniform01 region := by
    rw [uniform01, Measure.map_apply restrictedUnit clamp01 clamp01_measurable measurable,
      restrictedUnit, Measure.restrict_apply volume unitSet (clamp01_measurable measurable)]
    apply Measure.measure_eq_of_null_difference
    · apply volume.null_empty.mono
      intro value member
      exact member.2 ⟨member.1.2, member.1.1.1.1, member.1.1.2⟩
    · apply Measure.NullSet.mono
        (show volume.NullSet (Set.singleton Dedekind.zero) from volume_singleton Dedekind.zero)
      intro value member
      apply Dedekind.le_antisymm _ member.1.2.1
      exact not_lt_iff_le.mp (fun positiveValue =>
        member.2 ⟨⟨positiveValue, member.1.2.2⟩, member.1.1⟩)
  change volume inside = _
  rw [← unit, scaled, ← ENNReal.mul_assoc, ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]

/-! ### Failure codes in the unit interval -/

/-- Unit-interval codes of target points: the standard-Borel embedding into the
real line, then the real line's embedding into the open unit interval. -/
@[expose] noncomputable def code (presentation : StandardBorel target) :
    MeasurableEmbedding target unitBorel :=
  presentation.embeddingReal.trans StandardBorel.real.embedding

/-- No target point is coded by zero, which marks failure. -/
theorem code_ne_zero (presentation : StandardBorel target) (point : beta) :
    (code presentation).function point ≠ unitZero := by
  intro equal
  have positive := (StandardBorel.Real.encode_mem (presentation.embeddingReal.function point)).1
  have value := congrArg Subtype.val equal
  change StandardBorel.Real.encode (presentation.embeddingReal.function point) =
    Dedekind.zero at value
  rw [value] at positive
  exact positive.2 (Dedekind.le_refl _)

/-- Reads a code back: the coded point on the range, failure elsewhere. -/
@[expose] noncomputable def decode (embedding : MeasurableEmbedding target unitBorel)
    (value : UnitInterval) : Sum Unit beta := by
  classical
  exact if member : Set.range embedding.function value then Sum.inr (Classical.choose member)
    else Sum.inl ()

theorem decode_of_mem (embedding : MeasurableEmbedding target unitBorel) {value : UnitInterval}
    (member : Set.range embedding.function value) :
    ∃ point, embedding.function point = value ∧ decode embedding value = Sum.inr point := by
  classical
  refine ⟨Classical.choose member, Classical.choose_spec member, ?_⟩
  unfold decode
  rw [dite_eq_left member]

theorem decode_of_not_mem (embedding : MeasurableEmbedding target unitBorel)
    {value : UnitInterval} (outside : ¬Set.range embedding.function value) :
    decode embedding value = Sum.inl () := by
  classical
  unfold decode
  rw [dite_eq_right outside]

theorem decode_apply (embedding : MeasurableEmbedding target unitBorel) (point : beta) :
    decode embedding (embedding.function point) = Sum.inr point := by
  rcases decode_of_mem embedding ⟨point, rfl⟩ with ⟨found, coded, decoded⟩
  rw [decoded, embedding.injective coded]

/-- A code decodes into a region of the target exactly on the region's image. -/
theorem decode_preimage_inr (embedding : MeasurableEmbedding target unitBorel)
    (region : Set beta) :
    Set.preimage (decode embedding) (Set.image Sum.inr region) =
      Set.image embedding.function region := by
  apply Set.ext
  intro value
  constructor
  · rintro ⟨point, member, decoded⟩
    by_cases inRange : Set.range embedding.function value
    · rcases decode_of_mem embedding inRange with ⟨found, coded, equal⟩
      rw [equal] at decoded
      cases decoded
      exact ⟨point, member, coded⟩
    · rw [decode_of_not_mem embedding inRange] at decoded
      cases decoded
  · rintro ⟨point, member, rfl⟩
    exact ⟨point, member, (decode_apply embedding point).symm⟩

theorem decode_measurable (embedding : MeasurableEmbedding target unitBorel) :
    MeasurableMap unitBorel (Space.sum (Space.discrete Unit) target) (decode embedding) := by
  classical
  intro region measurable
  let defined := Set.image embedding.function (Set.preimage Sum.inr region)
  have definedMeasurable : unitBorel.Measurable defined :=
    embedding.image_measurable _ measurable.2
  have defined_iff : ∀ value, Set.range embedding.function value →
      (region (decode embedding value) ↔ defined value) := by
    intro value inRange
    rcases decode_of_mem embedding inRange with ⟨point, coded, decoded⟩
    rw [decoded]
    constructor
    · intro member
      exact ⟨point, member, coded⟩
    · rintro ⟨other, member, otherCoded⟩
      rw [← embedding.injective (otherCoded.trans coded.symm)]
      exact member
  by_cases failing : region (Sum.inl ())
  · have equal : Set.preimage (decode embedding) region =
        Set.union defined (Set.complement (Set.range embedding.function)) := by
      apply Set.ext
      intro value
      by_cases inRange : Set.range embedding.function value
      · rw [show Set.preimage (decode embedding) region value =
          region (decode embedding value) from rfl, defined_iff value inRange]
        exact ⟨Or.inl, fun member => member.elim id (fun outside => (outside inRange).elim)⟩
      · change region (decode embedding value) ↔ _
        rw [decode_of_not_mem embedding inRange]
        exact ⟨fun _ => Or.inr inRange, fun _ => failing⟩
    rw [equal]
    exact unitBorel.union definedMeasurable
      (unitBorel.complement embedding.range_measurable)
  · have equal : Set.preimage (decode embedding) region = defined := by
      apply Set.ext
      intro value
      by_cases inRange : Set.range embedding.function value
      · exact defined_iff value inRange
      · change region (decode embedding value) ↔ _
        rw [decode_of_not_mem embedding inRange]
        refine ⟨fun member => (failing member).elim, ?_⟩
        rintro ⟨point, _, coded⟩
        exact (inRange ⟨point, coded⟩).elim
    rw [equal]
    exact definedMeasurable

/-! ### Padding a subprobability kernel with a failure code -/

/-- The coded kernel plus its missing mass at zero, the failure code. -/
@[expose] noncomputable def padded (kernel : Kernel source target)
    (embedding : MeasurableEmbedding target unitBorel) : Kernel source unitBorel where
  toFun := fun input => Measure.add ((kernel input).map embedding.function embedding.measurable)
    (Measure.smul (ENNReal.sub ENNReal.one (kernel input Set.univ))
      (Measure.dirac unitBorel unitZero))
  measurable := by
    intro region measurable
    have equal : (fun input => Measure.add
          ((kernel input).map embedding.function embedding.measurable)
          (Measure.smul (ENNReal.sub ENNReal.one (kernel input Set.univ))
            (Measure.dirac unitBorel unitZero)) region) =
        fun input => ENNReal.add (kernel input (Set.preimage embedding.function region))
          (ENNReal.mul (ENNReal.sub ENNReal.one (kernel input Set.univ))
            (Measure.dirac unitBorel unitZero region)) := by
      funext input
      rw [Measure.add_apply_measurable _ _ measurable, Measure.map_apply _ _ _ measurable,
        Measure.smul_apply_measurable _ _ measurable]
    rw [equal]
    exact ENNRealMeasurable.add (kernel.measurable (embedding.measurable measurable))
      (ENNRealMeasurable.mul_const (ENNRealMeasurable.sub
        (ENNRealMeasurable.constant source ENNReal.one) (kernel.measurable target.univ)) _)

theorem padded_isProbability (kernel : Kernel source target)
    (embedding : MeasurableEmbedding target unitBorel) {input : alpha}
    (bounded : ENNReal.le (kernel input Set.univ) ENNReal.one) :
    Measure.IsProbability (padded kernel embedding input) := by
  constructor
  change Measure.add ((kernel input).map embedding.function embedding.measurable)
    (Measure.smul (ENNReal.sub ENNReal.one (kernel input Set.univ))
      (Measure.dirac unitBorel unitZero)) Set.univ = ENNReal.one
  rw [Measure.add_apply_measurable _ _ unitBorel.univ, Measure.map_apply _ _ _ unitBorel.univ,
    Set.preimage_univ, Measure.smul_apply_measurable _ _ unitBorel.univ,
    Measure.dirac_apply_univ, ENNReal.mul_one, ENNReal.add_comm]
  exact ENNReal.sub_add_cancel bounded

/-- On coded regions the padded kernel is the original kernel. -/
theorem padded_apply_image (kernel : Kernel source target)
    (embedding : MeasurableEmbedding target unitBorel)
    (avoids : ∀ point, embedding.function point ≠ unitZero) (input : alpha)
    {region : Set beta} (measurable : target.Measurable region) :
    padded kernel embedding input (Set.image embedding.function region) =
      kernel input region := by
  have imageMeasurable := embedding.image_measurable region measurable
  change Measure.add ((kernel input).map embedding.function embedding.measurable)
    (Measure.smul (ENNReal.sub ENNReal.one (kernel input Set.univ))
      (Measure.dirac unitBorel unitZero)) (Set.image embedding.function region) = _
  rw [Measure.add_apply_measurable _ _ imageMeasurable, Measure.map_apply _ _ _ imageMeasurable,
    Set.preimage_image _ embedding.injective, Measure.smul_apply_measurable _ _ imageMeasurable,
    Measure.dirac_apply_of_not_mem _ _ imageMeasurable
      (fun ⟨point, _, coded⟩ => avoids point coded),
    ENNReal.mul_zero, ENNReal.add_zero]

/-! ### Assembling the strips -/

section Assembly

variable {kernel : Kernel source target} (sfinite : IsSFinite kernel)

/-- A finite bound of the `index`th component. -/
@[expose] noncomputable def bound (index : Nat) : ENNReal :=
  Classical.choose (sfinite.finite index).exists_bound

theorem bound_spec (index : Nat) :
    ENNReal.Finite (bound sfinite index) ∧
      ∀ input, ENNReal.le (sfinite.components index input Set.univ) (bound sfinite index) :=
  Classical.choose_spec (sfinite.finite index).exists_bound

/-- The width of the `index`th strip, one more than its component's bound. -/
@[expose] noncomputable def width (index : Nat) : Carrier :=
  Dedekind.add (ENNReal.toReal (bound sfinite index)) Dedekind.one

theorem width_positive (index : Nat) : Dedekind.lt Dedekind.zero (width sfinite index) := by
  have nonnegative : Dedekind.le Dedekind.zero (ENNReal.toReal (bound sfinite index)) := by
    cases bound sfinite index with
    | top => exact Dedekind.le_refl _
    | finite value => exact value.property
  unfold width
  real_grind

/-- The left end of the `index`th strip: the strips are laid end to end from zero. -/
@[expose] noncomputable def offset : Nat → Carrier
  | 0 => Dedekind.zero
  | index + 1 => Dedekind.add (offset index) (width sfinite index)

/-- The `index`th strip. -/
@[expose] def piece (index : Nat) : Set Carrier :=
  strip (offset sfinite index) (width sfinite index)

theorem offset_after (index : Nat) :
    ∀ extra, Dedekind.le (Dedekind.add (offset sfinite index) (width sfinite index))
      (offset sfinite (index + 1 + extra))
  | 0 => Dedekind.le_refl _
  | extra + 1 => by
      have before := offset_after index extra
      have positive := width_positive sfinite (index + 1 + extra)
      change Dedekind.le _ (Dedekind.add (offset sfinite (index + 1 + extra))
        (width sfinite (index + 1 + extra)))
      real_grind

theorem piece_disjoint_of_lt {first second : Nat} (less : first < second) :
    Set.Disjoint (piece sfinite first) (piece sfinite second) := by
  intro value inFirst inSecond
  have firstBounds := strip_bounds (width_positive sfinite first) inFirst
  have secondBounds := strip_bounds (width_positive sfinite second) inSecond
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt less
  have ordered := offset_after sfinite first extra
  real_grind

theorem piece_pairwiseDisjoint : Set.PairwiseDisjoint (piece sfinite) := by
  intro first second different
  rcases Nat.lt_or_gt_of_ne different with less | greater
  · exact piece_disjoint_of_lt sfinite less
  · exact fun value inFirst inSecond => piece_disjoint_of_lt sfinite greater inSecond inFirst

/-- One plus the index of the strip that holds a seed, or zero outside every strip. -/
@[expose] noncomputable def pieceIndex (value : Carrier) : Nat := by
  classical
  exact if found : ∃ index, piece sfinite index value then Classical.choose found + 1 else 0

theorem pieceIndex_eq_succ_iff (value : Carrier) (index : Nat) :
    pieceIndex sfinite value = index + 1 ↔ piece sfinite index value := by
  classical
  unfold pieceIndex
  by_cases found : ∃ index, piece sfinite index value
  · rw [dite_eq_left found]
    have chosen := Classical.choose_spec found
    constructor
    · intro equal
      rw [← Nat.add_right_cancel equal]
      exact chosen
    · intro member
      apply congrArg (· + 1)
      apply Classical.byContradiction
      intro different
      exact piece_pairwiseDisjoint sfinite _ _ different chosen member
  · rw [dite_eq_right found]
    exact ⟨fun equal => (Nat.succ_ne_zero index equal.symm).elim,
      fun member => (found ⟨index, member⟩).elim⟩

theorem pieceIndex_eq_zero_iff (value : Carrier) :
    pieceIndex sfinite value = 0 ↔ ∀ index, ¬piece sfinite index value := by
  constructor
  · intro equal index member
    rw [(pieceIndex_eq_succ_iff sfinite value index).mpr member] at equal
    exact Nat.succ_ne_zero index equal
  · intro outside
    cases count : pieceIndex sfinite value with
    | zero => rfl
    | succ index =>
        exact ((outside index) ((pieceIndex_eq_succ_iff sfinite value index).mp count)).elim

theorem pieceIndex_fiber_measurable (index : Nat) :
    borel.Measurable (fun value => pieceIndex sfinite value = index) := by
  cases index with
  | zero =>
      have equal : (fun value => pieceIndex sfinite value = 0) =
          Set.complement (Set.iUnion (piece sfinite)) := by
        apply Set.ext
        intro value
        rw [pieceIndex_eq_zero_iff]
        exact ⟨fun outside ⟨index, member⟩ => outside index member,
          fun outside index member => outside ⟨index, member⟩⟩
      rw [equal]
      exact borel.complement (borel.iUnion (fun index => strip_measurable _ _))
  | succ index =>
      have equal : (fun value => pieceIndex sfinite value = index + 1) = piece sfinite index :=
        Set.ext (fun value => pieceIndex_eq_succ_iff sfinite value index)
      rw [equal]
      exact strip_measurable _ _

variable (presentation : StandardBorel target)

/-- The `index`th component scaled by the inverse width, a subprobability kernel. -/
@[expose] noncomputable def scaled (index : Nat) : Kernel source target :=
  Kernel.smul (ENNReal.ofReal (Dedekind.inverse (width sfinite index)))
    (sfinite.components index)

theorem scaled_bounded (index : Nat) (input : alpha) :
    ENNReal.le (scaled sfinite index input Set.univ) ENNReal.one := by
  have positive := width_positive sfinite index
  have finite := (bound_spec sfinite index).1
  have below : ENNReal.le (sfinite.components index input Set.univ)
      (ENNReal.ofReal (width sfinite index)) := by
    refine ENNReal.le_trans ((bound_spec sfinite index).2 input) ?_
    rw [← ENNReal.ofReal_toReal finite]
    apply ENNReal.ofReal_monotone
    have nonnegative : Dedekind.le Dedekind.zero (ENNReal.toReal (bound sfinite index)) := by
      rcases ENNReal.exists_finite_of_finite finite with ⟨value, equal⟩
      rw [equal]
      exact value.property
    unfold width
    real_grind
  change ENNReal.le (Measure.smul _ (sfinite.components index input) Set.univ) _
  rw [Measure.smul_apply_measurable _ _ target.univ, ← ofReal_mul_ofReal_inverse positive,
    ENNReal.mul_comm (ENNReal.ofReal (width sfinite index))]
  exact ENNReal.mul_le_mul_left below _

/-- The uniform randomizer of the `index`th padded component. -/
@[expose] noncomputable def pieceRandomizer (index : Nat) :
    Randomizer (padded (scaled sfinite index) (code presentation)) :=
  Randomizer.ofUnitInterval _
    (fun _ => padded_isProbability _ _ (scaled_bounded sfinite index _))

/-- The assembled map on the `index`th strip; `branch 0` is failure. -/
@[expose] noncomputable def branch : Nat → alpha × Carrier → Sum Unit beta
  | 0, _ => Sum.inl ()
  | index + 1, pair => decode (code presentation)
      ((pieceRandomizer sfinite presentation index).function
        (pair.1, stripSeed (offset sfinite index) (width sfinite index) pair.2))

/-- The partial map: each seed runs the randomizer of the strip that holds it. -/
@[expose] noncomputable def assembled (pair : alpha × Carrier) : Sum Unit beta :=
  branch sfinite presentation (pieceIndex sfinite pair.2) pair

theorem assembled_measurable :
    MeasurableMap (Space.product source borel) (Space.sum (Space.discrete Unit) target)
      (assembled sfinite presentation) := by
  have partitionMeasurable : ∀ index, (Space.product source borel).Measurable
      (fun pair : alpha × Carrier => pieceIndex sfinite pair.2 = index) := fun index =>
    Space.second_measurable source borel (pieceIndex_fiber_measurable sfinite index)
  have branchesMeasurable : ∀ index, MeasurableMap (Space.product source borel)
      (Space.sum (Space.discrete Unit) target) (branch sfinite presentation index) := by
    intro index
    cases index with
    | zero => exact MeasurableMap.constant _ _ _
    | succ index =>
        exact MeasurableMap.comp (decode_measurable (code presentation))
          (MeasurableMap.comp (pieceRandomizer sfinite presentation index).measurable
            (Space.pair_measurable (Space.first_measurable source borel)
              (MeasurableMap.comp (stripSeed_measurable _ _)
                (Space.second_measurable source borel))))
  show MeasurableMap _ _ (fun pair => branch sfinite presentation (pieceIndex sfinite pair.2) pair)
  intro set setMeasurable
  exact MeasurableMap.countable_piecewise (partition := fun pair => pieceIndex sfinite pair.2)
    (branches := branch sfinite presentation) partitionMeasurable branchesMeasurable setMeasurable

/-- Seeds that land in a coded region, strip by strip. -/
theorem assembled_preimage (input : alpha) (region : Set beta) :
    Set.preimage (fun seed => assembled sfinite presentation (input, seed))
        (Set.image Sum.inr region) =
      Set.iUnion (fun index => Set.inter (piece sfinite index)
        (Set.preimage (stripSeed (offset sfinite index) (width sfinite index))
          (Set.preimage (fun seed => (pieceRandomizer sfinite presentation index).function
            (input, seed)) (Set.image (code presentation).function region)))) := by
  apply Set.ext
  intro value
  change Set.image Sum.inr region
      (branch sfinite presentation (pieceIndex sfinite value) (input, value)) ↔ _
  cases count : pieceIndex sfinite value with
  | zero =>
      have outside := (pieceIndex_eq_zero_iff sfinite value).mp count
      constructor
      · rintro ⟨_, _, impossible⟩
        cases impossible
      · rintro ⟨index, member, _⟩
        exact (outside index member).elim
  | succ index =>
      have inside := (pieceIndex_eq_succ_iff sfinite value index).mp count
      change Set.preimage (decode (code presentation)) (Set.image Sum.inr region) _ ↔ _
      rw [decode_preimage_inr]
      constructor
      · intro member
        exact ⟨index, inside, member⟩
      · rintro ⟨other, otherInside, member⟩
        have same : other = index := Nat.add_right_cancel
          (((pieceIndex_eq_succ_iff sfinite value other).mpr otherInside).symm.trans count)
        subst same
        exact member

end Assembly

/-- Every s-finite kernel into a standard-Borel space has a partial Lebesgue
randomizer. The parameter space is arbitrary, fibres may have infinite mass,
and zero kernels or an empty target fail everywhere. -/
@[expose] noncomputable def ofSFinite (kernel : Kernel source target)
    (presentation : StandardBorel target) (sfinite : IsSFinite kernel) :
    PartialRandomizer kernel where
  function := assembled sfinite presentation
  measurable := assembled_measurable sfinite presentation
  law := by
    intro input
    apply Measure.ext
    intro region measurable
    have codedMeasurable := (code presentation).image_measurable region measurable
    rw [Measure.comap_apply _ _ measurable,
      Measure.map_apply _ _ _ ((MeasurableEmbedding.inr _ _).image_measurable region measurable)]
    change volume (Set.preimage (fun seed => assembled sfinite presentation (input, seed))
      (Set.image Sum.inr region)) = _
    rw [assembled_preimage, Measure.iUnion_disjoint]
    · have term : ∀ index, volume (Set.inter (piece sfinite index)
          (Set.preimage (stripSeed (offset sfinite index) (width sfinite index))
            (Set.preimage (fun seed => (pieceRandomizer sfinite presentation index).function
              (input, seed)) (Set.image (code presentation).function region)))) =
          sfinite.components index input region := by
        intro index
        have positive := width_positive sfinite index
        have stripVolume := volume_strip (offset sfinite index) positive
          (((pieceRandomizer sfinite presentation index).fiber_measurable input) codedMeasurable)
        rw [show piece sfinite index = strip (offset sfinite index) (width sfinite index) from rfl,
          stripVolume]
        have uniform := congrArg (fun measure : Measure unitBorel =>
          measure (Set.image (code presentation).function region))
          ((pieceRandomizer sfinite presentation index).law input)
        rw [Measure.map_apply _ _ _ codedMeasurable] at uniform
        rw [uniform, padded_apply_image _ _ (code_ne_zero presentation) input measurable]
        change ENNReal.mul _ (Measure.smul _ (sfinite.components index input) region) = _
        rw [Measure.smul_apply_measurable _ _ measurable, ← ENNReal.mul_assoc,
          ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]
      rw [ENNReal.tsum_congr term, ← Measure.sum_apply _ measurable, ← Kernel.sum_apply,
        sfinite.sum_eq]
    · intro index
      exact borel.inter (strip_measurable _ _)
        (stripSeed_measurable _ _ (((pieceRandomizer sfinite presentation index).fiber_measurable
          input) codedMeasurable))
    · intro first second different value inFirst inSecond
      exact piece_pairwiseDisjoint sfinite first second different inFirst.1 inSecond.1

/-- The law read at a measurable region: the volume of seeds landing in it. -/
theorem law_apply {kernel : Kernel source target} (randomizer : PartialRandomizer kernel)
    (input : alpha) {region : Set beta} (measurable : target.Measurable region) :
    volume (Set.preimage (fun seed => randomizer.function (input, seed))
      (Set.image Sum.inr region)) = kernel input region := by
  rw [← randomizer.law input, Measure.comap_apply _ _ measurable,
    Measure.map_apply _ _ _ ((MeasurableEmbedding.inr _ _).image_measurable region measurable)]
  rfl

end PartialRandomizer

end

end Problib.Measure.Kernel
