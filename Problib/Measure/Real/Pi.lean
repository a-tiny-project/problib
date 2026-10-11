module
public import Problib.Measure.Real.Affine
public import Problib.Measure.Pi
public import Problib.Measure.Kernel.Product.Transport
public import Problib.Measure.Kernel.Product.Finite
public import Problib.Measure.Kernel.Measurable.Section
public import Problib.Measure.Integral.Lebesgue.Transport

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

end
end Problib.Measure.Real
