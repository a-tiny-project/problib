module

public import Problib.Analysis.PAP.AnalyticSet
public import Problib.Analysis.Real.FiniteVector.Basis

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

public theorem analytic_on_neg {dimension : Nat}
    {region : Set (carrier dimension)}
    {function : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => neg (function point)) := by
  have scaled := analytic_on_scale analytic (neg one)
  simpa only [neg_mul, one_mul] using scaled

public theorem analytic_on_sub {dimension : Nat}
    {region : Set (carrier dimension)}
    {first second : carrier dimension → selection.Carrier}
    (firstAnalytic : AnalyticOn region first)
    (secondAnalytic : AnalyticOn region second) :
    AnalyticOn region (fun point => sub (first point) (second point)) := by
  have combined := analytic_on_add firstAnalytic
    (analytic_on_neg secondAnalytic)
  simpa only [sub_eq_add_neg] using combined

private theorem sub_nonpositive_iff {first second : selection.Carrier} :
    le (sub first second) zero ↔ le first second := by
  constructor
  · intro nonpositive
    have shifted := (add_le_add_right_iff (shift := second)).mpr nonpositive
    rwa [sub_add_cancel, zero_add] at shifted
  · intro included
    apply (add_le_add_right_iff (shift := second)).mp
    rwa [sub_add_cancel, zero_add]

@[expose] public def boxLowerConstraint {dimension : Nat}
    (lower : carrier dimension) (coordinate : Fin dimension) :
    carrier dimension → selection.Carrier :=
  fun point => sub (lower coordinate) (point coordinate)

@[expose] public def boxUpperConstraint {dimension : Nat}
    (upper : carrier dimension) (coordinate : Fin dimension) :
    carrier dimension → selection.Carrier :=
  fun point => sub (point coordinate) (upper coordinate)

@[expose] public def boxConstraints {dimension : Nat}
    (lower upper : carrier dimension) :
    List (carrier dimension → selection.Carrier) :=
  (List.finRange dimension).map (boxLowerConstraint lower) ++
    (List.finRange dimension).map (boxUpperConstraint upper)

public theorem boxConstraints_analytic {dimension : Nat}
    (lower upper : carrier dimension) :
    ∀ constraint, constraint ∈ boxConstraints lower upper →
      AnalyticOn (Set.univ : Set (carrier dimension)) constraint := by
  intro constraint member
  rcases List.mem_append.mp member with lowerMember | upperMember
  · rcases List.mem_map.mp lowerMember with ⟨coordinate, _, equal⟩
    subst constraint
    exact analytic_on_sub
      (analytic_on_constant (is_open_univ dimension) (lower coordinate))
      (analytic_on_coordinate (is_open_univ dimension) coordinate)
  · rcases List.mem_map.mp upperMember with ⟨coordinate, _, equal⟩
    subst constraint
    exact analytic_on_sub
      (analytic_on_coordinate (is_open_univ dimension) coordinate)
      (analytic_on_constant (is_open_univ dimension) (upper coordinate))

public theorem boxConstraints_character {dimension : Nat}
    (lower upper : carrier dimension) (point : carrier dimension) :
    closedBox lower upper point ↔
      ∀ constraint, constraint ∈ boxConstraints lower upper →
        le (constraint point) zero := by
  constructor
  · intro inside constraint member
    rcases List.mem_append.mp member with lowerMember | upperMember
    · rcases List.mem_map.mp lowerMember with ⟨coordinate, _, equal⟩
      subst constraint
      exact sub_nonpositive_iff.mpr (inside coordinate).1
    · rcases List.mem_map.mp upperMember with ⟨coordinate, _, equal⟩
      subst constraint
      exact sub_nonpositive_iff.mpr (inside coordinate).2
  · intro bounded coordinate
    have inRange := List.mem_finRange coordinate
    constructor
    · apply sub_nonpositive_iff.mp
      exact bounded (boxLowerConstraint lower coordinate)
        (List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨coordinate, inRange, rfl⟩)))
    · apply sub_nonpositive_iff.mp
      exact bounded (boxUpperConstraint upper coordinate)
        (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨coordinate, inRange, rfl⟩)))

/-- Each rational closed box is analytic using its finitely many coordinate
inequalities on the whole carrier. -/
public theorem closedBox_analytic {dimension : Nat}
    (lower upper : carrier dimension) :
    AnalyticSet (closedBox lower upper) := by
  let lowerConstraint (coordinate : Fin dimension) :
      carrier dimension → selection.Carrier :=
    fun point => sub (lower coordinate) (point coordinate)
  let upperConstraint (coordinate : Fin dimension) :
      carrier dimension → selection.Carrier :=
    fun point => sub (point coordinate) (upper coordinate)
  let constraints :=
    (List.finRange dimension).map lowerConstraint ++
      (List.finRange dimension).map upperConstraint
  refine ⟨Set.univ, constraints, is_open_univ dimension, ?_, ?_⟩
  · intro constraint member
    rcases List.mem_append.mp member with lowerMember | upperMember
    · rcases List.mem_map.mp lowerMember with ⟨coordinate, _, equal⟩
      subst constraint
      exact analytic_on_sub
        (analytic_on_constant (is_open_univ dimension) (lower coordinate))
        (analytic_on_coordinate (is_open_univ dimension) coordinate)
    · rcases List.mem_map.mp upperMember with ⟨coordinate, _, equal⟩
      subst constraint
      exact analytic_on_sub
        (analytic_on_coordinate (is_open_univ dimension) coordinate)
        (analytic_on_constant (is_open_univ dimension) (upper coordinate))
  · intro point
    change closedBox lower upper point ↔
      (True ∧ ∀ constraint, constraint ∈ constraints →
        le (constraint point) zero)
    constructor
    · intro inside
      refine ⟨True.intro, fun constraint member => ?_⟩
      rcases List.mem_append.mp member with lowerMember | upperMember
      · rcases List.mem_map.mp lowerMember with ⟨coordinate, _, equal⟩
        subst constraint
        exact sub_nonpositive_iff.mpr (inside coordinate).1
      · rcases List.mem_map.mp upperMember with ⟨coordinate, _, equal⟩
        subst constraint
        exact sub_nonpositive_iff.mpr (inside coordinate).2
    · rintro ⟨_, bounded⟩
      intro coordinate
      have inRange := List.mem_finRange coordinate
      constructor
      · apply sub_nonpositive_iff.mp
        exact bounded (lowerConstraint coordinate)
          (List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨coordinate, inRange, rfl⟩)))
      · apply sub_nonpositive_iff.mp
        exact bounded (upperConstraint coordinate)
          (List.mem_append.mpr (Or.inr
            (List.mem_map.mpr ⟨coordinate, inRange, rfl⟩)))

/-- A guarded analytic piece uses a closed box wholly inside the open domain
of its local analytic inequalities. An inactive record denotes the empty set
and permits a uniform Nat-indexed family of boxes. -/
public structure BoxedAnalytic {dimension : Nat}
    (points : Set (carrier dimension)) where
  active : Prop
  lower : carrier dimension
  upper : carrier dimension
  region : Set (carrier dimension)
  open_region : IsOpen region
  box_inside : active → Set.Subset (closedBox lower upper) region
  constraints : List (carrier dimension → selection.Carrier)
  analytic_constraints : ∀ constraint, constraint ∈ constraints →
    AnalyticOn region constraint
  character : ∀ point, points point ↔
    active ∧ closedBox lower upper point ∧
      ∀ constraint, constraint ∈ constraints →
        le (constraint point) zero

public theorem BoxedAnalytic.analytic {dimension : Nat}
    {points : Set (carrier dimension)}
    (boxed : BoxedAnalytic points) : AnalyticSet points := by
  by_cases active : boxed.active
  · let core : Set (carrier dimension) := fun point =>
      boxed.region point ∧
        ∀ constraint, constraint ∈ boxed.constraints →
          le (constraint point) zero
    have coreAnalytic : AnalyticSet core := by
      exact ⟨boxed.region, boxed.constraints, boxed.open_region,
        boxed.analytic_constraints, fun _ => Iff.rfl⟩
    have intersection := analytic_set_inter
      (closedBox_analytic boxed.lower boxed.upper) coreAnalytic
    have equal : points = Set.inter
        (closedBox boxed.lower boxed.upper) core := by
      apply Set.ext
      intro point
      rw [boxed.character point]
      change (boxed.active ∧ closedBox boxed.lower boxed.upper point ∧
        (∀ constraint, constraint ∈ boxed.constraints →
          le (constraint point) zero)) ↔
        (closedBox boxed.lower boxed.upper point ∧
          boxed.region point ∧
          (∀ constraint, constraint ∈ boxed.constraints →
            le (constraint point) zero))
      constructor
      · rintro ⟨_, inBox, bounds⟩
        exact ⟨inBox, boxed.box_inside active inBox, bounds⟩
      · rintro ⟨inBox, _, bounds⟩
        exact ⟨active, inBox, bounds⟩
    rw [equal]
    exact intersection
  · have equal : points = Set.empty := by
      apply Set.ext
      intro point
      rw [boxed.character point]
      exact ⟨fun member => False.elim (active member.1),
        fun impossible => False.elim impossible⟩
    rw [equal]
    exact analytic_set_empty dimension

/-- Rational closed boxes refine an arbitrary analytic set into countably
many guarded analytic pieces. -/
public theorem analytic_set_box_cover {dimension : Nat}
    {points : Set (carrier dimension)} (analytic : AnalyticSet points) :
    ∃ pieces : Nat → Set (carrier dimension),
      (∀ index, Nonempty (BoxedAnalytic (pieces index))) ∧
        points = Set.iUnion pieces := by
  classical
  rcases analytic with ⟨region, constraints, openRegion,
    analyticConstraints, character⟩
  let lower (index : Nat) : carrier dimension :=
    rationalCenter dimension (Problib.Countable.Pair.decode index).1
  let upper (index : Nat) : carrier dimension :=
    rationalCenter dimension (Problib.Countable.Pair.decode index).2
  let active (index : Nat) : Prop :=
    Set.Subset (closedBox (lower index) (upper index)) region
  let pieces (index : Nat) : Set (carrier dimension) :=
    fun point => active index ∧
      closedBox (lower index) (upper index) point ∧
      ∀ constraint, constraint ∈ constraints → le (constraint point) zero
  refine ⟨pieces, ?_, ?_⟩
  · intro index
    exact ⟨{
      active := active index
      lower := lower index
      upper := upper index
      region := region
      open_region := openRegion
      box_inside := fun included => included
      constraints := constraints
      analytic_constraints := analyticConstraints
      character := fun _ => Iff.rfl
    }⟩
  · apply Set.ext
    intro point
    constructor
    · intro member
      rcases (character point).mp member with ⟨inRegion, bounds⟩
      rcases exists_rational_closedBox_inside openRegion inRegion with
        ⟨lowerCode, upperCode, inBox, boxInside⟩
      let index := Problib.Countable.Pair.encode (lowerCode, upperCode)
      refine ⟨index, ?_⟩
      change active index ∧ closedBox (lower index) (upper index) point ∧
        ∀ constraint, constraint ∈ constraints → le (constraint point) zero
      have corner : Problib.Countable.Pair.decode index =
          (lowerCode, upperCode) :=
        Problib.Countable.Pair.decode_encode _
      simp only [active, lower, upper, corner] at *
      exact ⟨boxInside, inBox, bounds⟩
    · rintro ⟨index, activeBox, inBox, bounds⟩
      apply (character point).mpr
      exact ⟨activeBox inBox, bounds⟩

end Problib.Analysis.PAP
