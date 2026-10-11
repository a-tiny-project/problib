module

public import Problib.Measure.Equivalence.Preserving
public import Problib.Measure.Real.Pi
public import Problib.Inference.SplitMerge.Strength

set_option autoImplicit false

/-!
# The centroid split

Richardson and Green's split keeps the parent's strength and its centroid. A
patch is a strength, a mean in `ℝ^d` and a shape. The split draws a fraction
`v`, a mean offset `u` and two child shapes. The children are
`(vα, m + (1 − v)u, Σ₁)` and `((1 − v)α, m + (1 − v)u − u, Σ₂)`, and the parent
shape is kept on the merge side. So the merge recovers every split input, and
the pairing is an involution by construction.

The pairing is a composite. A coordinate shuffle comes first. The mean block
then shears by the fraction, which preserves volume on each fibre. The
strength block splits the strength (`strengthSplit`), and a second shuffle
lays out the children. Only the strength block changes the reference, so the
Jacobian is `1 / (α₁ + α₂)` (`centroidPairing_reference_change`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel volume volumeSFinite volumePi volumePiSFinite
  translatePi translatePi_measurable negPi negPi_measurable map_volumePi_translate
  map_volumePi_neg measurable_add measurable_mul measurable_sub neg_measurable)

universe u

variable {γ : Type u}

public section

/-- Means in dimension `dimension`. -/
abbrev meanSpace (dimension : Nat) : Space (Fin dimension → Carrier) :=
  Space.pi (fun _ : Fin dimension => borel)

/-- A pair of means. -/
abbrev meanPlane (dimension : Nat) :
    Space ((Fin dimension → Carrier) × (Fin dimension → Carrier)) :=
  Space.product (meanSpace dimension) (meanSpace dimension)

/-- Volume on a pair of means. -/
@[expose] noncomputable def meanVolume (dimension : Nat) : Measure (meanPlane dimension) :=
  Measure.prod (volumePi dimension) (volumePi dimension) (volumePiSFinite dimension)

@[expose] noncomputable def meanVolumeSFinite (dimension : Nat) :
    Measure.SFinite (meanVolume dimension) :=
  (volumePiSFinite dimension).prod (volumePiSFinite dimension)

private theorem add_neg_add_neg (left right : Carrier) :
    Dedekind.add left (Dedekind.neg (Dedekind.add left (Dedekind.neg right))) = right := by
  rw [Dedekind.neg_add, Dedekind.neg_neg, ← Dedekind.add_assoc, Dedekind.add_neg,
    Dedekind.zero_add]

private theorem neg_add_cancel_left (shift value : Carrier) :
    Dedekind.add (Dedekind.neg shift) (Dedekind.add shift value) = value := by
  rw [← Dedekind.add_assoc, Dedekind.add_comm (Dedekind.neg shift) shift, Dedekind.add_neg,
    Dedekind.zero_add]

/-- Each coordinate of a mean is measurable. -/
theorem meanSpace_coordinate_measurable {dimension : Nat} (index : Fin dimension) :
    MeasurableMap (meanSpace dimension) borel (fun point => point index) :=
  Space.coordinate_measurable (fun _ : Fin dimension => borel) index

/-- Each coordinate of the first mean in a pair is measurable. -/
theorem meanFirst_coordinate_measurable {dimension : Nat} (index : Fin dimension) :
    MeasurableMap (Space.product (meanSpace dimension) (meanSpace dimension)) borel
      (fun point => point.1 index) :=
  MeasurableMap.comp (meanSpace_coordinate_measurable index) (Space.first_measurable _ _)

/-- Each coordinate of the second mean in a pair is measurable. -/
theorem meanSecond_coordinate_measurable {dimension : Nat} (index : Fin dimension) :
    MeasurableMap (Space.product (meanSpace dimension) (meanSpace dimension)) borel
      (fun point => point.2 index) :=
  MeasurableMap.comp (meanSpace_coordinate_measurable index) (Space.second_measurable _ _)

/-- Shear a pair of means by a fraction: the first mean moves by the fraction
of the offset, and the second is the first less the offset. -/
@[expose] noncomputable def meanShear (dimension : Nat) (fraction : Carrier) :
    MeasurableEquivalence (meanPlane dimension) (meanPlane dimension) where
  forward := fun pair =>
    (fun index => Dedekind.add (Dedekind.mul fraction (pair.2 index)) (pair.1 index),
      fun index => Dedekind.add
        (Dedekind.add (Dedekind.mul fraction (pair.2 index)) (pair.1 index))
        (Dedekind.neg (pair.2 index)))
  inverse := fun pair =>
    (fun index => Dedekind.add
        (Dedekind.neg (Dedekind.mul fraction
          (Dedekind.add (pair.1 index) (Dedekind.neg (pair.2 index)))))
        (pair.1 index),
      fun index => Dedekind.add (pair.1 index) (Dedekind.neg (pair.2 index)))
  inverse_forward := by
    rintro ⟨mean, offset⟩
    have recovered : (fun index => Dedekind.add
        (Dedekind.add (Dedekind.mul fraction (offset index)) (mean index))
        (Dedekind.neg (Dedekind.add
          (Dedekind.add (Dedekind.mul fraction (offset index)) (mean index))
          (Dedekind.neg (offset index))))) = offset :=
      funext fun index => add_neg_add_neg _ _
    apply Prod.ext
    · funext index
      change Dedekind.add (Dedekind.neg (Dedekind.mul fraction
          (Dedekind.add (Dedekind.add (Dedekind.mul fraction (offset index)) (mean index))
            (Dedekind.neg (Dedekind.add
              (Dedekind.add (Dedekind.mul fraction (offset index)) (mean index))
              (Dedekind.neg (offset index)))))))
          (Dedekind.add (Dedekind.mul fraction (offset index)) (mean index)) = mean index
      rw [add_neg_add_neg, neg_add_cancel_left]
    · exact recovered
  forward_inverse := by
    rintro ⟨first, second⟩
    have restored : (fun index => Dedekind.add
        (Dedekind.mul fraction (Dedekind.add (first index) (Dedekind.neg (second index))))
        (Dedekind.add (Dedekind.neg (Dedekind.mul fraction
          (Dedekind.add (first index) (Dedekind.neg (second index))))) (first index))) =
        first := by
      funext index
      rw [← Dedekind.add_assoc, Dedekind.add_neg, Dedekind.zero_add]
    apply Prod.ext
    · exact restored
    · funext index
      change Dedekind.add
          (Dedekind.add (Dedekind.mul fraction
            (Dedekind.add (first index) (Dedekind.neg (second index))))
            (Dedekind.add (Dedekind.neg (Dedekind.mul fraction
              (Dedekind.add (first index) (Dedekind.neg (second index))))) (first index)))
          (Dedekind.neg (Dedekind.add (first index) (Dedekind.neg (second index)))) =
        second index
      rw [← Dedekind.add_assoc (Dedekind.mul fraction _), Dedekind.add_neg, Dedekind.zero_add,
        add_neg_add_neg]
  forward_measurable := by
   exact Space.pair_measurable
    (Space.pi_measurable fun index => measurable_add
      (measurable_mul (MeasurableMap.constant _ _ fraction)
        (meanSecond_coordinate_measurable index))
      (meanFirst_coordinate_measurable index))
    (Space.pi_measurable fun index => measurable_add
      (measurable_add
        (measurable_mul (MeasurableMap.constant _ _ fraction)
          (meanSecond_coordinate_measurable index))
        (meanFirst_coordinate_measurable index))
      (MeasurableMap.comp neg_measurable
        (meanSecond_coordinate_measurable index)))
  inverse_measurable := by
   exact Space.pair_measurable
    (Space.pi_measurable fun index => measurable_add
      (MeasurableMap.comp neg_measurable
        (measurable_mul (MeasurableMap.constant _ _ fraction)
          (measurable_add
            (meanFirst_coordinate_measurable index)
            (MeasurableMap.comp neg_measurable
              (meanSecond_coordinate_measurable index)))))
      (meanFirst_coordinate_measurable index))
    (Space.pi_measurable fun index => measurable_add
      (meanFirst_coordinate_measurable index)
      (MeasurableMap.comp neg_measurable
        (meanSecond_coordinate_measurable index)))

/-- Moving the first mean by a multiple of the offset preserves volume. -/
@[expose] noncomputable def shiftFirst (dimension : Nat) (fraction : Carrier) :
    MeasurePreserving (meanVolume dimension) (meanVolume dimension) :=
  let shift := MeasurePreserving.fibre (volumePi dimension) (volumePi dimension)
    (volumePiSFinite dimension)
    (fun offset mean index => Dedekind.add (Dedekind.mul fraction (offset index)) (mean index))
    (fun offset mean index =>
      Dedekind.add (Dedekind.neg (Dedekind.mul fraction (offset index))) (mean index))
    (Space.pi_measurable fun index => measurable_add
      (measurable_mul (MeasurableMap.constant _ _ fraction)
        (meanFirst_coordinate_measurable index))
      (meanSecond_coordinate_measurable index))
    (Space.pi_measurable fun index => measurable_add
      (MeasurableMap.comp neg_measurable
        (measurable_mul (MeasurableMap.constant _ _ fraction)
          (meanFirst_coordinate_measurable index)))
      (meanSecond_coordinate_measurable index))
    (fun _ _ => funext fun _ => by exact neg_add_cancel_left _ _)
    (fun _ _ => funext fun _ => by
      rw [← Dedekind.add_assoc, Dedekind.add_neg, Dedekind.zero_add])
    (fun offset => map_volumePi_translate dimension
      (fun index => Dedekind.mul fraction (offset index)))
  ((MeasurePreserving.swap (volumePi dimension) (volumePi dimension)
      (volumePiSFinite dimension) (volumePiSFinite dimension)).trans shift).trans
    (MeasurePreserving.swap (volumePi dimension) (volumePi dimension)
      (volumePiSFinite dimension) (volumePiSFinite dimension))

/-- Replacing the offset by the first mean less the offset preserves volume. -/
@[expose] noncomputable def reflectSecond (dimension : Nat) :
    MeasurePreserving (meanVolume dimension) (meanVolume dimension) :=
  MeasurePreserving.fibre (volumePi dimension) (volumePi dimension) (volumePiSFinite dimension)
    (fun first offset index => Dedekind.add (first index) (Dedekind.neg (offset index)))
    (fun first offset index => Dedekind.add (first index) (Dedekind.neg (offset index)))
    (Space.pi_measurable fun index => measurable_add
      (meanFirst_coordinate_measurable index)
      (MeasurableMap.comp neg_measurable
        (meanSecond_coordinate_measurable index)))
    (Space.pi_measurable fun index => measurable_add
      (meanFirst_coordinate_measurable index)
      (MeasurableMap.comp neg_measurable
        (meanSecond_coordinate_measurable index)))
    (fun _ _ => funext fun _ => by exact add_neg_add_neg _ _)
    (fun _ _ => funext fun _ => by exact add_neg_add_neg _ _)
    (fun first => by
      calc
        (volumePi dimension).map
            (fun offset index => Dedekind.add (first index) (Dedekind.neg (offset index)))
            (MeasurableMap.comp (translatePi_measurable dimension first)
              (negPi_measurable dimension)) =
          ((volumePi dimension).map (negPi dimension) (negPi_measurable dimension)).map
            (translatePi dimension first) (translatePi_measurable dimension first) :=
            (Measure.map_comp _ _ _ (negPi_measurable dimension)
              (translatePi_measurable dimension first)).symm
        _ = volumePi dimension := by
            rw [map_volumePi_neg, map_volumePi_translate])

/-- The mean shear preserves volume on a pair of means. -/
@[expose] noncomputable def meanShearPreserving (dimension : Nat) (fraction : Carrier) :
    MeasurePreserving (meanVolume dimension) (meanVolume dimension) :=
  ((shiftFirst dimension fraction).trans (reflectSecond dimension)).congr
    (meanShear dimension fraction) (fun _ => rfl)


/-- The mean shear is measurable jointly in a measurable fraction and pair. -/
theorem meanShear_forward_measurable {δ : Type u} {input : Space δ} {dimension : Nat}
    {fraction : δ → Carrier}
    {pair : δ → (Fin dimension → Carrier) × (Fin dimension → Carrier)}
    (fractionMeasurable : MeasurableMap input borel fraction)
    (pairMeasurable : MeasurableMap input (meanPlane dimension) pair) :
    MeasurableMap input (meanPlane dimension)
      (fun point => (meanShear dimension (fraction point)).forward (pair point)) := by
  have offset : ∀ index : Fin dimension,
      MeasurableMap input borel (fun point => (pair point).2 index) := fun index =>
    MeasurableMap.comp (meanSpace_coordinate_measurable index)
      (MeasurableMap.comp (Space.second_measurable _ _) pairMeasurable)
  have mean : ∀ index : Fin dimension,
      MeasurableMap input borel (fun point => (pair point).1 index) := fun index =>
    MeasurableMap.comp (meanSpace_coordinate_measurable index)
      (MeasurableMap.comp (Space.first_measurable _ _) pairMeasurable)
  show MeasurableMap input (meanPlane dimension) (fun point =>
    (fun index => Dedekind.add (Dedekind.mul (fraction point) ((pair point).2 index))
        ((pair point).1 index),
      fun index => Dedekind.add
        (Dedekind.add (Dedekind.mul (fraction point) ((pair point).2 index))
          ((pair point).1 index))
        (Dedekind.neg ((pair point).2 index))))
  exact Space.pair_measurable
    (Space.pi_measurable fun index =>
      measurable_add (measurable_mul fractionMeasurable (offset index)) (mean index))
    (Space.pi_measurable fun index => measurable_add
      (measurable_add (measurable_mul fractionMeasurable (offset index)) (mean index))
      (MeasurableMap.comp neg_measurable (offset index)))

/-- The inverse mean shear is measurable jointly in a measurable fraction and
pair. -/
theorem meanShear_inverse_measurable {δ : Type u} {input : Space δ} {dimension : Nat}
    {fraction : δ → Carrier}
    {pair : δ → (Fin dimension → Carrier) × (Fin dimension → Carrier)}
    (fractionMeasurable : MeasurableMap input borel fraction)
    (pairMeasurable : MeasurableMap input (meanPlane dimension) pair) :
    MeasurableMap input (meanPlane dimension)
      (fun point => (meanShear dimension (fraction point)).inverse (pair point)) := by
  have gap : ∀ index : Fin dimension, MeasurableMap input borel
      (fun point => Dedekind.add ((pair point).1 index) (Dedekind.neg ((pair point).2 index))) :=
    fun index => measurable_add
      (MeasurableMap.comp (meanSpace_coordinate_measurable index)
        (MeasurableMap.comp (Space.first_measurable _ _) pairMeasurable))
      (MeasurableMap.comp neg_measurable (MeasurableMap.comp (meanSpace_coordinate_measurable index)
        (MeasurableMap.comp (Space.second_measurable _ _) pairMeasurable)))
  show MeasurableMap input (meanPlane dimension) (fun point =>
    (fun index => Dedekind.add
        (Dedekind.neg (Dedekind.mul (fraction point)
          (Dedekind.add ((pair point).1 index) (Dedekind.neg ((pair point).2 index)))))
        ((pair point).1 index),
      fun index => Dedekind.add ((pair point).1 index) (Dedekind.neg ((pair point).2 index))))
  exact Space.pair_measurable
    (Space.pi_measurable fun index => measurable_add
      (MeasurableMap.comp neg_measurable (measurable_mul fractionMeasurable (gap index)))
      (MeasurableMap.comp (meanSpace_coordinate_measurable index)
        (MeasurableMap.comp (Space.first_measurable _ _) pairMeasurable)))
    (Space.pi_measurable gap)

variable {σ : Type u} {shapes : Space σ}

/-- A patch: a strength, a mean and a shape. -/
abbrev patchSpace (dimension : Nat) (shapes : Space σ) :
    Space (Carrier × ((Fin dimension → Carrier) × σ)) :=
  Space.product borel (Space.product (meanSpace dimension) shapes)

/-- The split's draw: a fraction, a mean offset and two child shapes. -/
abbrev splitDraw (dimension : Nat) (shapes : Space σ) :
    Space ((Carrier × (Fin dimension → Carrier)) × (σ × σ)) :=
  Space.product (Space.product borel (meanSpace dimension)) (Space.product shapes shapes)

/-- The shapes left beside the strengths and the means: the two child shapes
and the parent shape. -/
abbrev shapeTriple (shapes : Space σ) : Space ((σ × σ) × σ) :=
  Space.product (Space.product shapes shapes) shapes

/-- The middle layout: the strength plane, the mean plane and the shapes. -/
abbrev centroidMiddle (dimension : Nat) (shapes : Space σ) :
    Space ((Carrier × Carrier) × (((Fin dimension → Carrier) × (Fin dimension → Carrier)) ×
      ((σ × σ) × σ))) :=
  Space.product strengthPlane (Space.product (meanPlane dimension) (shapeTriple shapes))

variable (dimension : Nat) (shapeReference : Measure shapes)
  (shapeFinite : Measure.SFinite shapeReference)

/-- Reference on a patch: volume on the strength and the mean, and the shape
reference. -/
@[expose] noncomputable def patchReference : Measure (patchSpace dimension shapes) :=
  Measure.prod volume (Measure.prod (volumePi dimension) shapeReference shapeFinite)
    ((volumePiSFinite dimension).prod shapeFinite)

@[expose] noncomputable def patchReferenceSFinite :
    Measure.SFinite (patchReference dimension shapeReference shapeFinite) :=
  volumeSFinite.prod ((volumePiSFinite dimension).prod shapeFinite)

/-- Reference on the split side: a parent patch and the split's draw. -/
@[expose] noncomputable def centroidSplitReference :
    Measure (Space.product (patchSpace dimension shapes) (splitDraw dimension shapes)) :=
  Measure.prod (patchReference dimension shapeReference shapeFinite)
    (Measure.prod (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension))
      (Measure.prod shapeReference shapeReference shapeFinite) (shapeFinite.prod shapeFinite))
    ((volumeSFinite.prod (volumePiSFinite dimension)).prod (shapeFinite.prod shapeFinite))

/-- Reference on the merge side: two child patches and the kept parent shape. -/
@[expose] noncomputable def centroidMergeReference :
    Measure (Space.product
      (Space.product (patchSpace dimension shapes) (patchSpace dimension shapes)) shapes) :=
  Measure.prod
    (Measure.prod (patchReference dimension shapeReference shapeFinite)
      (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite))
    shapeReference shapeFinite

/-- Reference on the middle layout. -/
@[expose] noncomputable def centroidMiddleReference :
    Measure (centroidMiddle dimension shapes) :=
  Measure.prod planeVolume
    (Measure.prod (meanVolume dimension)
      (Measure.prod (Measure.prod shapeReference shapeReference shapeFinite) shapeReference
        shapeFinite)
      ((shapeFinite.prod shapeFinite).prod shapeFinite))
    ((meanVolumeSFinite dimension).prod ((shapeFinite.prod shapeFinite).prod shapeFinite))

/-- Lay the split side out as strengths, means and shapes:
`((α, (m, Σ)), ((v, u), (Σ₁, Σ₂)))` goes to `((α, v), ((m, u), ((Σ₁, Σ₂), Σ)))`. -/
@[expose] noncomputable def centroidGather :
    MeasurePreserving (centroidSplitReference dimension shapeReference shapeFinite)
      (centroidMiddleReference dimension shapeReference shapeFinite) :=
  let pairs := Measure.prod shapeReference shapeReference shapeFinite
  let pairsFinite := shapeFinite.prod shapeFinite
  let meanShape := Measure.prod (volumePi dimension) shapeReference shapeFinite
  let meanShapeFinite := (volumePiSFinite dimension).prod shapeFinite
  let meanPairs := Measure.prod (volumePi dimension) pairs pairsFinite
  let meanPairsFinite := (volumePiSFinite dimension).prod pairsFinite
  let splitOffset := MeasurePreserving.product
    ((volumeSFinite.prod (volumePiSFinite dimension)).prod pairsFinite)
    (volumeSFinite.prod meanPairsFinite)
    (MeasurePreserving.refl (patchReference dimension shapeReference shapeFinite))
    (MeasurePreserving.associate volume (volumePi dimension) pairs (volumePiSFinite dimension)
      pairsFinite)
  let strengths := MeasurePreserving.interchange volume meanShape volume meanPairs
    meanShapeFinite volumeSFinite meanPairsFinite
  let means := MeasurePreserving.product
    (meanShapeFinite.prod meanPairsFinite)
    ((volumePiSFinite dimension).prod (volumePiSFinite dimension) |>.prod
      (shapeFinite.prod pairsFinite))
    (MeasurePreserving.refl planeVolume)
    (MeasurePreserving.interchange (volumePi dimension) shapeReference (volumePi dimension) pairs
      shapeFinite (volumePiSFinite dimension) pairsFinite)
  let shapesLast := MeasurePreserving.product
    (((volumePiSFinite dimension).prod (volumePiSFinite dimension)).prod
      (shapeFinite.prod pairsFinite))
    ((meanVolumeSFinite dimension).prod (pairsFinite.prod shapeFinite))
    (MeasurePreserving.refl planeVolume)
    (MeasurePreserving.product (shapeFinite.prod pairsFinite) (pairsFinite.prod shapeFinite)
      (MeasurePreserving.refl (meanVolume dimension))
      (MeasurePreserving.swap shapeReference pairs shapeFinite pairsFinite))
  ((splitOffset.trans strengths).trans means).trans shapesLast

/-- The fraction left to the first child's mean. -/
@[expose] noncomputable def remainder (point : Carrier × Carrier) : Carrier :=
  Dedekind.sub Dedekind.one point.2

theorem remainder_measurable : MeasurableMap strengthPlane borel remainder :=
  measurable_sub (MeasurableMap.constant strengthPlane borel _) (Space.second_measurable _ _)

/-- Shear the means by the remaining fraction, fibre by fibre over the
strength plane. -/
@[expose] noncomputable def centroidShear :
    MeasurePreserving (centroidMiddleReference dimension shapeReference shapeFinite)
      (centroidMiddleReference dimension shapeReference shapeFinite) :=
  let restFinite := (shapeFinite.prod shapeFinite).prod shapeFinite
  let rest := Measure.prod (Measure.prod shapeReference shapeReference shapeFinite)
    shapeReference shapeFinite
  MeasurePreserving.fibre planeVolume (Measure.prod (meanVolume dimension) rest restFinite)
    ((meanVolumeSFinite dimension).prod restFinite)
    (fun base pair => ((meanShear dimension (remainder base)).forward pair.1, pair.2))
    (fun base pair => ((meanShear dimension (remainder base)).inverse pair.1, pair.2))
    (Space.pair_measurable
      (meanShear_forward_measurable
        (MeasurableMap.comp remainder_measurable (Space.first_measurable _ _))
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _)))
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))
    (Space.pair_measurable
      (meanShear_inverse_measurable
        (MeasurableMap.comp remainder_measurable (Space.first_measurable _ _))
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _)))
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))
    (fun base pair => Prod.ext ((meanShear dimension (remainder base)).inverse_forward pair.1)
      rfl)
    (fun base pair => Prod.ext ((meanShear dimension (remainder base)).forward_inverse pair.1)
      rfl)
    (fun base => (MeasurePreserving.product restFinite restFinite
      (meanShearPreserving dimension (remainder base)) (MeasurePreserving.refl rest)).preserves)

/-- Lay the strengths, means and shapes out as two child patches and the kept
parent shape: `((α₁, α₂), ((m₁, m₂), ((Σ₁, Σ₂), Σ)))` goes to
`(((α₁, (m₁, Σ₁)), (α₂, (m₂, Σ₂))), Σ)`. -/
@[expose] noncomputable def centroidScatter :
    MeasurePreserving (centroidMiddleReference dimension shapeReference shapeFinite)
      (centroidMergeReference dimension shapeReference shapeFinite) :=
  let pairs := Measure.prod shapeReference shapeReference shapeFinite
  let pairsFinite := shapeFinite.prod shapeFinite
  let meanShape := Measure.prod (volumePi dimension) shapeReference shapeFinite
  let meanShapeFinite := (volumePiSFinite dimension).prod shapeFinite
  let children := Measure.prod meanShape meanShape meanShapeFinite
  let childrenFinite := meanShapeFinite.prod meanShapeFinite
  let splitShapes := MeasurePreserving.product
    ((meanVolumeSFinite dimension).prod (pairsFinite.prod shapeFinite))
    (((meanVolumeSFinite dimension).prod pairsFinite).prod shapeFinite)
    (MeasurePreserving.refl planeVolume)
    (MeasurePreserving.associate (meanVolume dimension) pairs shapeReference pairsFinite
      shapeFinite).symm
  let pairUp := MeasurePreserving.product
    (((meanVolumeSFinite dimension).prod pairsFinite).prod shapeFinite)
    (childrenFinite.prod shapeFinite)
    (MeasurePreserving.refl planeVolume)
    (MeasurePreserving.product shapeFinite shapeFinite
      (MeasurePreserving.interchange (volumePi dimension) (volumePi dimension) shapeReference
        shapeReference (volumePiSFinite dimension) shapeFinite shapeFinite)
      (MeasurePreserving.refl shapeReference))
  let lastShape := (MeasurePreserving.associate planeVolume children shapeReference
    childrenFinite shapeFinite).symm
  let patches := MeasurePreserving.product shapeFinite shapeFinite
    (MeasurePreserving.interchange volume volume meanShape meanShape volumeSFinite
      meanShapeFinite meanShapeFinite)
    (MeasurePreserving.refl shapeReference)
  ((splitShapes.trans pairUp).trans lastShape).trans patches

/-- The centroid split: a parent patch and a draw `(v, u, Σ₁, Σ₂)` go to the
children `(vα, m + (1 − v)u, Σ₁)` and `((1 − v)α, m + (1 − v)u − u, Σ₂)`, with
the parent shape kept. -/
@[expose] noncomputable def centroidPairing :
    MeasurablePartialEquivalence
      (Space.product (patchSpace dimension shapes) (splitDraw dimension shapes))
      (Space.product
        (Space.product (patchSpace dimension shapes) (patchSpace dimension shapes)) shapes) :=
  (MeasurablePartialEquivalence.ofEquivalence
    ((centroidGather dimension shapeReference shapeFinite).trans
      (centroidShear dimension shapeReference shapeFinite)).equivalence).trans
    ((strengthSplit.productRight (Space.product (meanPlane dimension) (shapeTriple shapes))).trans
      (MeasurablePartialEquivalence.ofEquivalence
        (centroidScatter dimension shapeReference shapeFinite).equivalence))

/-- The centroid split's Jacobian, read on the merge side: one over the sum of
the child strengths. -/
@[expose] noncomputable def centroidJacobian
    (point : ((Carrier × ((Fin dimension → Carrier) × σ)) ×
      (Carrier × ((Fin dimension → Carrier) × σ))) × σ) : Carrier :=
  strengthJacobian (point.1.1.1, point.1.2.1)

private theorem reference_change_factor {δ ε : Type u} {source : Space δ} {target : Space ε}
    {pairing : MeasurablePartialEquivalence source target}
    {sourceReference : Measure source} {targetReference : Measure target}
    {factor other : ε → Carrier} (same : ∀ value, factor value = other value)
    (change : pairing.ReferenceChange sourceReference targetReference factor) :
    pairing.ReferenceChange sourceReference targetReference other :=
  (funext same : factor = other) ▸ change

/-- The centroid split changes reference by one over the sum of the child
strengths. -/
theorem centroidPairing_reference_change :
    (centroidPairing dimension shapeReference shapeFinite).ReferenceChange
      (centroidSplitReference dimension shapeReference shapeFinite)
      (centroidMergeReference dimension shapeReference shapeFinite)
      (centroidJacobian dimension) := by
  let scatter := centroidScatter dimension shapeReference shapeFinite
  have unitMeasurable : ∀ {δ : Type u} (space : Space δ),
      MeasurableMap space borel (fun _ => Dedekind.one) := fun space =>
    MeasurableMap.constant space borel _
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have splitChange := MeasurablePartialEquivalence.reference_change_productRight
    (rest := Space.product (meanPlane dimension) (shapeTriple shapes))
    (Measure.prod (meanVolume dimension)
      (Measure.prod (Measure.prod shapeReference shapeReference shapeFinite) shapeReference
        shapeFinite)
      ((shapeFinite.prod shapeFinite).prod shapeFinite))
    ((meanVolumeSFinite dimension).prod ((shapeFinite.prod shapeFinite).prod shapeFinite))
    strengthJacobian_measurable strengthSplit_reference_change
  have splitMeasurable : MeasurableMap (centroidMiddle dimension shapes) borel
      (fun value => strengthJacobian value.1) :=
    MeasurableMap.comp strengthJacobian_measurable (Space.first_measurable _ _)
  have later := MeasurablePartialEquivalence.reference_change_trans splitMeasurable
    (unitMeasurable _) splitChange scatter.reference_change
    (fun value inside => Dedekind.inverse_nonnegative
      (Dedekind.le_of_lt (Dedekind.add_positive inside.1 inside.2)))
    (fun _ _ => unitNonnegative)
  have laterMeasurable : MeasurableMap
      (Space.product (Space.product (patchSpace dimension shapes) (patchSpace dimension shapes))
        shapes) borel
      (fun value => Dedekind.mul Dedekind.one
        (strengthJacobian (scatter.equivalence.inverse value).1)) :=
    measurable_mul (unitMeasurable _) (MeasurableMap.comp splitMeasurable
      scatter.equivalence.inverse_measurable)
  have whole := MeasurablePartialEquivalence.reference_change_trans (unitMeasurable _)
    laterMeasurable
    ((centroidGather dimension shapeReference shapeFinite).trans
      (centroidShear dimension shapeReference shapeFinite)).reference_change later
    (fun _ _ => unitNonnegative)
    (fun value inside => by
      change Dedekind.le Dedekind.zero (Dedekind.mul Dedekind.one
        (strengthJacobian (scatter.equivalence.inverse value).1))
      rw [Dedekind.one_mul]
      exact Dedekind.inverse_nonnegative
        (Dedekind.le_of_lt (Dedekind.add_positive inside.2.1 inside.2.2)))
  refine reference_change_factor ?_ whole
  intro value
  change Dedekind.mul (Dedekind.mul Dedekind.one
    (strengthJacobian (value.1.1.1, value.1.2.1))) Dedekind.one =
      strengthJacobian (value.1.1.1, value.1.2.1)
  rw [Dedekind.mul_one, Dedekind.one_mul]

/-- The centroid Jacobian is measurable on the merge side. -/
theorem centroidJacobian_measurable :
    MeasurableMap
      (Space.product
        (Space.product (patchSpace dimension shapes) (patchSpace dimension shapes)) shapes)
      borel (centroidJacobian (σ := σ) dimension) := by
  intro set setMeasurable
  exact (MeasurableMap.comp strengthJacobian_measurable
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _)))
      (MeasurableMap.comp (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _)))))
    setMeasurable

/-- On the merge side of the centroid split both child strengths are positive,
so the Jacobian is nonnegative. -/
theorem centroidJacobian_nonnegative
    {point : ((Carrier × ((Fin dimension → Carrier) × σ)) ×
      (Carrier × ((Fin dimension → Carrier) × σ))) × σ}
    (inside : (centroidPairing dimension shapeReference shapeFinite).targetDomain point) :
    Dedekind.le Dedekind.zero (centroidJacobian dimension point) := by
  have positive : Dedekind.lt Dedekind.zero point.1.1.1 ∧
      Dedekind.lt Dedekind.zero point.1.2.1 := inside.1.2
  exact Dedekind.inverse_nonnegative
    (Dedekind.le_of_lt (Dedekind.add_positive positive.1 positive.2))

theorem centroidJacobian_positive
    {point : ((Carrier × ((Fin dimension → Carrier) × σ)) ×
      (Carrier × ((Fin dimension → Carrier) × σ))) × σ}
    (inside : (centroidPairing dimension shapeReference shapeFinite).targetDomain point) :
    Dedekind.lt Dedekind.zero (centroidJacobian dimension point) := by
  have positive : Dedekind.lt Dedekind.zero point.1.1.1 ∧
      Dedekind.lt Dedekind.zero point.1.2.1 := inside.1.2
  exact Dedekind.inverse_of_positive_positive (Dedekind.add_positive positive.1 positive.2)

end
end Problib.Inference
