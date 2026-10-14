module
public import Problib.Measure.Real.Affine
public import Problib.Measure.Pi
public import Problib.Measure.Kernel.Product.Transport
public import Problib.Measure.Kernel.Product.Finite
public import Problib.Measure.Kernel.Measurable.Section
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Analysis.Real.FiniteVector.Concatenation

set_option autoImplicit false
namespace Problib.Measure.Real
open Problib.Real
public section
universe u v w x

@[expose] public def finCons (dimension : Nat)
    (pair : Carrier × (Fin dimension → Carrier)) :
    Fin (dimension + 1) → Carrier :=
  fun index => Fin.cases pair.1 pair.2 index

/-- Prepending a coordinate is measurable. -/
public theorem finCons_measurable (dimension : Nat) :
    MeasurableMap
      (Space.product borel (Space.pi (fun _ : Fin dimension => borel)))
      (Space.pi (fun _ : Fin (dimension + 1) => borel))
      (finCons dimension) := by
  apply Space.pi_measurable
  intro index
  refine Fin.cases ?_ ?_ index
  · exact Space.first_measurable _ _
  · intro earlier
    exact MeasurableMap.comp
      (Space.coordinate_measurable (fun _ : Fin dimension => borel) earlier)
      (Space.second_measurable _ _)

@[expose] public noncomputable def volumePiWithFinite :
    (dimension : Nat) →
      Σ law : Measure (Space.pi (fun _ : Fin dimension => borel)),
        Measure.SFinite law
  | 0 =>
      ⟨Measure.dirac _ (fun index => Fin.elim0 index),
        Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)⟩
  | dimension + 1 =>
      let previous := volumePiWithFinite dimension
      let law := (Measure.prod volume previous.1 previous.2).map
        (finCons dimension)
          (finCons_measurable dimension)
      ⟨law, (Measure.SFinite.prod volumeSFinite previous.2).map
        (finCons dimension)
          (finCons_measurable dimension)⟩

/-- Finite product of Dedekind Lebesgue volume in every dimension. -/
@[expose] public noncomputable def volumePi (dimension : Nat) :
    Measure (Space.pi (fun _ : Fin dimension => borel)) :=
  (volumePiWithFinite dimension).1

@[expose] public noncomputable def volumePiSFinite (dimension : Nat) :
    Measure.SFinite (volumePi dimension) :=
  (volumePiWithFinite dimension).2

/-- Zero-dimensional volume is the unit mass at the empty coordinate map. -/
public theorem volumePi_zero :
    volumePi 0 = Measure.dirac _ (fun index => Fin.elim0 index) := rfl

/-- Volume in dimension `dimension + 1` prepends a Lebesgue coordinate to
volume in dimension `dimension`. -/
public theorem volumePi_succ (dimension : Nat) :
    volumePi (dimension + 1) =
      (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map
        (finCons dimension) (finCons_measurable dimension) := rfl

/-- Volume on `dimension` coordinates is the finite product of one Lebesgue lane
per coordinate, read at any input. -/
public theorem finProduct_const_volume {α : Type u} (source : Space α) :
    (dimension : Nat) → (input : α) →
    Kernel.finProduct dimension (fun _ => Kernel.const source volume)
        (fun _ => Kernel.IsSFinite.const source volumeSFinite) input =
      volumePi dimension
  | 0, input => Kernel.finProduct_dirac 0 _ _ (values := fun lane => lane.elim0)
      fun lane => lane.elim0
  | dimension + 1, input => by
      rw [Kernel.finProduct_succ_apply, volumePi_succ,
        Measure.prod_congr_right _ _ (volumePiSFinite dimension)
          (finProduct_const_volume source dimension input)]
      rfl

@[expose] public def translatePi (dimension : Nat) (shift : Fin dimension → Carrier)
    (point : Fin dimension → Carrier) : Fin dimension → Carrier :=
  fun index => Problib.Real.Construction.Dedekind.add (shift index) (point index)

public theorem translatePi_measurable (dimension : Nat)
    (shift : Fin dimension → Carrier) :
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel))
      (translatePi dimension shift) :=
  Space.pi_measurable (fun index =>
    MeasurableMap.comp (translate_measurable (shift index))
      (Space.coordinate_measurable (fun _ : Fin dimension => borel) index))

public theorem map_volumePi_translate (dimension : Nat)
    (shift : Fin dimension → Carrier) :
    (volumePi dimension).map (translatePi dimension shift)
      (translatePi_measurable dimension shift) = volumePi dimension := by
  induction dimension with
  | zero =>
      have equal : translatePi 0 shift = (fun point => point) := by
        funext point index
        exact Fin.elim0 index
      calc
        _ = (volumePi 0).map (fun point => point)
            (MeasurableMap.identity _) := Measure.map_congr_function _ _ _ equal
        _ = volumePi 0 := Measure.map_id _
  | succ dimension induction =>
      let head := fun value => Problib.Real.Construction.Dedekind.add (shift 0) value
      let tailShift : Fin dimension → Carrier := fun index => shift index.succ
      let tail := translatePi dimension tailShift
      have commute :
          (fun pair => translatePi (dimension + 1) shift (finCons dimension pair)) =
          (fun pair => finCons dimension (head pair.1, tail pair.2)) := by
        funext pair index
        refine Fin.cases ?_ ?_ index
        · rfl
        · intro earlier
          rfl
      calc
        (volumePi (dimension + 1)).map (translatePi (dimension + 1) shift)
            (translatePi_measurable (dimension + 1) shift) =
            ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map
              (finCons dimension) (finCons_measurable dimension)).map
                (translatePi (dimension + 1) shift)
                (translatePi_measurable (dimension + 1) shift) := rfl
        _ = (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map
              (fun pair => finCons dimension (head pair.1, tail pair.2))
                (MeasurableMap.comp (finCons_measurable dimension)
                  (Space.product_map (translate_measurable (shift 0))
                    (translatePi_measurable dimension tailShift))) := by
          calc
            _ = (Measure.prod volume (volumePi dimension)
                (volumePiSFinite dimension)).map
                (fun pair => translatePi (dimension + 1) shift
                  (finCons dimension pair))
                (MeasurableMap.comp
                  (translatePi_measurable (dimension + 1) shift)
                  (finCons_measurable dimension)) :=
              Measure.map_comp _ _ _ _ _
            _ = _ := Measure.map_congr_function _ _ _ commute
        _ = (Measure.prod (volume.map head (translate_measurable (shift 0)))
              ((volumePi dimension).map tail (translatePi_measurable dimension tailShift))
              ((volumePiSFinite dimension).map tail
                (translatePi_measurable dimension tailShift))).map
              (finCons dimension) (finCons_measurable dimension) := by
          calc
            _ = ((Measure.prod volume (volumePi dimension)
                (volumePiSFinite dimension)).map
                (fun pair => (head pair.1, tail pair.2))
                (Space.product_map (translate_measurable (shift 0))
                  (translatePi_measurable dimension tailShift))).map
                (finCons dimension) (finCons_measurable dimension) :=
              (Measure.map_comp _ _ _ _ _).symm
            _ = _ := by
              rw [Measure.prod_map volume (volumePi dimension) (volumePiSFinite dimension)
                head tail (translate_measurable (shift 0))
                (translatePi_measurable dimension tailShift)]
        _ = volumePi (dimension + 1) := by
          rw [map_volume_translate]
          have sameProduct := Measure.prod_congr_right volume
            ((volumePiSFinite dimension).map tail
              (translatePi_measurable dimension tailShift))
            (volumePiSFinite dimension) (induction tailShift)
          rw [sameProduct]
          rfl

@[expose] public def negPi (dimension : Nat)
    (point : Fin dimension → Carrier) : Fin dimension → Carrier :=
  fun index => Problib.Real.Construction.Dedekind.neg (point index)

public theorem negPi_measurable (dimension : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (negPi dimension) :=
  Space.pi_measurable (fun index =>
    MeasurableMap.comp neg_measurable
      (Space.coordinate_measurable (fun _ : Fin dimension => borel) index))

public theorem map_volumePi_neg (dimension : Nat) :
    (volumePi dimension).map (negPi dimension) (negPi_measurable dimension) =
      volumePi dimension := by
  induction dimension with
  | zero =>
      have equal : negPi 0 = (fun point => point) := by
        funext point index
        exact Fin.elim0 index
      calc
        _ = (volumePi 0).map (fun point => point)
            (MeasurableMap.identity _) := Measure.map_congr_function _ _ _ equal
        _ = volumePi 0 := Measure.map_id _
  | succ dimension induction =>
      have commute :
          (fun pair => negPi (dimension + 1) (finCons dimension pair)) =
          (fun pair => finCons dimension
            (Problib.Real.Construction.Dedekind.neg pair.1,
              negPi dimension pair.2)) := by
        funext pair index
        refine Fin.cases ?_ ?_ index
        · rfl
        · intro earlier
          rfl
      calc
        (volumePi (dimension + 1)).map (negPi (dimension + 1))
            (negPi_measurable (dimension + 1)) =
            ((Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map
              (finCons dimension) (finCons_measurable dimension)).map
                (negPi (dimension + 1)) (negPi_measurable (dimension + 1)) := rfl
        _ = (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension)).map
              (fun pair => finCons dimension
                (Problib.Real.Construction.Dedekind.neg pair.1,
                  negPi dimension pair.2))
              (MeasurableMap.comp (finCons_measurable dimension)
                (Space.product_map neg_measurable
                  (negPi_measurable dimension))) := by
          calc
            _ = (Measure.prod volume (volumePi dimension)
                (volumePiSFinite dimension)).map
                (fun pair => negPi (dimension + 1) (finCons dimension pair))
                (MeasurableMap.comp (negPi_measurable (dimension + 1))
                  (finCons_measurable dimension)) :=
              Measure.map_comp _ _ _ _ _
            _ = _ := Measure.map_congr_function _ _ _ commute
        _ = (Measure.prod
              (volume.map Problib.Real.Construction.Dedekind.neg neg_measurable)
              ((volumePi dimension).map (negPi dimension) (negPi_measurable dimension))
              ((volumePiSFinite dimension).map (negPi dimension)
                (negPi_measurable dimension))).map
              (finCons dimension) (finCons_measurable dimension) := by
          calc
            _ = ((Measure.prod volume (volumePi dimension)
                (volumePiSFinite dimension)).map
                (fun pair => (Problib.Real.Construction.Dedekind.neg pair.1,
                  negPi dimension pair.2))
                (Space.product_map neg_measurable
                  (negPi_measurable dimension))).map
                (finCons dimension) (finCons_measurable dimension) :=
              (Measure.map_comp _ _ _ _ _).symm
            _ = _ := by
              rw [Measure.prod_map volume (volumePi dimension) (volumePiSFinite dimension)
                Problib.Real.Construction.Dedekind.neg (negPi dimension)
                neg_measurable (negPi_measurable dimension)]
        _ = volumePi (dimension + 1) := by
          rw [map_volume_neg]
          have sameProduct := Measure.prod_congr_right volume
            ((volumePiSFinite dimension).map (negPi dimension)
              (negPi_measurable dimension))
            (volumePiSFinite dimension) induction
          rw [sameProduct]
          rfl

/-- Line volume carried to one-entry vectors. -/
@[expose] public def lineVector (value : Carrier) : Fin 1 → Carrier := fun _ => value

public theorem lineVector_measurable :
    MeasurableMap borel (Space.pi (fun _ : Fin 1 => borel)) lineVector :=
  Space.pi_measurable fun _ => MeasurableMap.identity borel

/-- Volume in one coordinate is line volume, carried to one-entry vectors. -/
public theorem volumePi_one : volumePi 1 = volume.map lineVector lineVector_measurable := by
  apply Measure.ext
  intro set setMeasurable
  have joint := finCons_measurable 0 setMeasurable
  have lineMeasurable := lineVector_measurable setMeasurable
  have asIntegral : volume (Set.preimage lineVector set) =
      lintegral volume (ennrealIndicator (Set.preimage lineVector set) (fun _ => ENNReal.one)) := by
    rw [lintegral_indicator _ _ lineMeasurable, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.one_mul]
  rw [volumePi_succ, Measure.map_apply _ _ _ setMeasurable, Measure.prod_apply _ _ _ joint,
    Measure.map_apply _ _ _ setMeasurable, asIntegral]
  congr 1
  funext value
  have point : finCons 0 (value, fun index => Fin.elim0 index) = lineVector value := by
    funext coordinate
    refine Fin.cases rfl (fun earlier => Fin.elim0 earlier) coordinate
  classical
  rw [volumePi_zero, Measure.dirac_apply _ _ (Kernel.pair_left_measurable value joint)]
  unfold ennrealIndicator ennrealPiecewise
  simp only [Set.preimage, point]
  congr

/-! ### Volume on concatenated coordinates -/

/-- Reindex a vector along an equality of dimensions. -/
@[expose] public def castVector {source target : Nat} (equal : source = target)
    (point : Fin source → Carrier) : Fin target → Carrier :=
  fun index => point (Fin.cast equal.symm index)

public theorem castVector_measurable {source target : Nat} (equal : source = target) :
    MeasurableMap (Space.pi (fun _ : Fin source => borel))
      (Space.pi (fun _ : Fin target => borel)) (castVector equal) :=
  Space.pi_measurable fun index =>
    Space.coordinate_measurable (fun _ : Fin source => borel) (Fin.cast equal.symm index)

/-- Volume is unchanged by reindexing along an equality of dimensions. -/
public theorem volumePi_cast {source target : Nat} (equal : source = target) :
    (volumePi source).map (castVector equal) (castVector_measurable equal) =
      volumePi target := by
  subst equal
  calc
    _ = (volumePi source).map (fun point => point) (MeasurableMap.identity _) :=
      Measure.map_congr_function _ _ _ (funext fun _ => rfl)
    _ = volumePi source := Measure.map_id _

/-- Concatenation, measurable for the coordinate spaces as this file names them. -/
private theorem concatenation_measurable (left right : Nat) :
    MeasurableMap
      (Space.product (Space.pi (fun _ : Fin left => borel)) (Space.pi (fun _ : Fin right => borel)))
      (Space.pi (fun _ : Fin (left + right) => borel))
      (fun pair => Problib.Analysis.Real.FiniteVector.pairVector pair.1 pair.2) :=
  Problib.Analysis.Real.FiniteVector.pairVector_measurable left right

/-- A product whose left factor is a unit mass is the right factor placed
beside that point. -/
private theorem prod_dirac_left {α : Type u} {β : Type v}
    {first : Space α} {second : Space β} (point : α)
    (law : Measure second) (finite : Measure.SFinite law) :
    Measure.prod (Measure.dirac first point) law finite =
      law.map (fun value => (point, value))
        (Space.pair_measurable (MeasurableMap.constant second first point)
          (MeasurableMap.identity second)) := by
  apply Measure.ext
  intro region regionMeasurable
  have sections : ENNRealMeasurable first
      (fun input => law (Set.preimage (fun value => (input, value)) region)) :=
    Kernel.section_apply_measurable (Kernel.const first law)
      (Kernel.IsSFinite.const first finite) regionMeasurable
  rw [Measure.prod_apply _ law finite regionMeasurable,
    lintegral_dirac first point sections,
    Measure.map_apply _ _ _ regionMeasurable]

/-- Prepending a coordinate to a concatenation prepends it to the first
block. -/
private theorem finCons_pairVector {left right : Nat} (head : Carrier)
    (first : Fin left → Carrier) (second : Fin right → Carrier)
    (equal : left + 1 + right = left + right + 1) (index : Fin (left + 1 + right)) :
    finCons (left + right)
        (head, Problib.Analysis.Real.FiniteVector.pairVector first second)
        (Fin.cast equal index) =
      Problib.Analysis.Real.FiniteVector.pairVector (finCons left (head, first)) second
        index := by
  refine Fin.addCases (fun early => ?_) (fun late => ?_) index
  · refine Fin.cases ?_ (fun earlier => ?_) early
    · have zero : Fin.cast equal (Fin.castAdd right (0 : Fin (left + 1))) = 0 :=
        Fin.ext rfl
      rw [zero]
      simp only [finCons, Problib.Analysis.Real.FiniteVector.pairVector,
        Fin.addCases_left, Fin.cases_zero]
    · have shifted : Fin.cast equal (Fin.castAdd right earlier.succ) =
          (Fin.castAdd right earlier).succ := Fin.ext rfl
      rw [shifted]
      simp only [finCons, Problib.Analysis.Real.FiniteVector.pairVector,
        Fin.addCases_left, Fin.cases_succ]
  · have shifted : Fin.cast equal (Fin.natAdd (left + 1) late) =
        (Fin.natAdd left late).succ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
    rw [shifted]
    simp only [finCons, Problib.Analysis.Real.FiniteVector.pairVector,
      Fin.addCases_right, Fin.cases_succ]

private theorem volumePi_add_cast (right : Nat) : (left target : Nat) →
    (equal : left + right = target) →
    volumePi target =
      (Measure.prod (volumePi left) (volumePi right) (volumePiSFinite right)).map
        (fun pair => castVector equal
          (Problib.Analysis.Real.FiniteVector.pairVector pair.1 pair.2))
        (MeasurableMap.comp (castVector_measurable equal)
          (concatenation_measurable left right))
  | 0, target, equal => by
      have shift : right = target := (Nat.zero_add right).symm.trans equal
      rw [← volumePi_cast shift, volumePi_zero, prod_dirac_left, Measure.map_comp]
      apply Measure.map_congr_function
      funext point index
      have moved : Fin.cast equal.symm index = Fin.natAdd 0 (Fin.cast shift.symm index) :=
        Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, Nat.zero_add])
      simp only [castVector, moved, Problib.Analysis.Real.FiniteVector.pairVector,
        Fin.addCases_right]
  | left + 1, target, equal => by
      have shift : left + right + 1 = target := by omega
      have regroup : left + 1 + right = left + right + 1 := by omega
      have previous := volumePi_add_cast right left (left + right) rfl
      rw [← volumePi_cast shift, volumePi_succ,
        Measure.prod_congr_right volume (volumePiSFinite (left + right))
          ((Measure.SFinite.prod (volumePiSFinite left) (volumePiSFinite right)).map _
            (MeasurableMap.comp (castVector_measurable rfl)
              (concatenation_measurable left right)))
          previous,
        Measure.prod_map_right, Measure.map_comp, Measure.map_comp,
        volumePi_succ left, Measure.prod_map_left, Measure.map_comp,
        Measure.prod_associate, Measure.map_comp]
      apply Measure.map_congr_function
      funext point index
      exact finCons_pairVector point.1 point.2.1 point.2.2 regroup
        (Fin.cast equal.symm index)

/-- Volume on concatenated coordinates is the product of the two blocks'
volumes, read through concatenation. -/
public theorem volumePi_add (left right : Nat) :
    volumePi (left + right) =
      (Measure.prod (volumePi left) (volumePi right) (volumePiSFinite right)).map
        (fun pair => Problib.Analysis.Real.FiniteVector.pairVector pair.1 pair.2)
        (Problib.Analysis.Real.FiniteVector.pairVector_measurable left right :
          MeasurableMap
            (Space.product (Space.pi (fun _ : Fin left => borel))
              (Space.pi (fun _ : Fin right => borel)))
            (Space.pi (fun _ : Fin (left + right) => borel)) _) :=
  (volumePi_add_cast right left (left + right) rfl).trans
    (Measure.map_congr_function _ _ _ (funext fun _ => rfl))

end
end Problib.Measure.Real
