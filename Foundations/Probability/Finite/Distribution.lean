import Foundations.Probability.Finite.PMF

namespace Foundations.Probability

universe u v w

def FiniteDistribution (α : Type u) :=
  Quotient (FinitePMF.equivalentSetoid α)

namespace FiniteDistribution

def ofPMF {α : Type u} (law : FinitePMF α) : FiniteDistribution α :=
  Quotient.mk _ law

def pure {α : Type u} (value : α) : FiniteDistribution α :=
  ofPMF (FinitePMF.dirac value)

noncomputable def representative {α : Type u}
    (law : FiniteDistribution α) : FinitePMF α :=
  Classical.choose (Quotient.exists_rep law)

theorem ofPMF_representative {α : Type u} (law : FiniteDistribution α) :
    ofPMF law.representative = law :=
  Classical.choose_spec (Quotient.exists_rep law)

theorem representative_equivalent {α : Type u} (law : FiniteDistribution α)
    (representative : FinitePMF α) (equal : ofPMF representative = law) :
    law.representative ≈ₚ representative :=
  Quotient.exact (Eq.trans law.ofPMF_representative equal.symm)

def map {α : Type u} {β : Type v} (transform : α → β) :
    FiniteDistribution α → FiniteDistribution β :=
  Quotient.lift
    (fun law => ofPMF (law.map transform))
    (fun _ _ equivalent => Quotient.sound
      (FinitePMF.Equivalent.map equivalent transform))

noncomputable def bind {α : Type u} {β : Type v}
    (law : FiniteDistribution α) (kernel : α → FiniteDistribution β) :
    FiniteDistribution β :=
  Quotient.lift
    (fun outer => ofPMF (outer.bind fun value => (kernel value).representative))
    (fun _ _ equivalent => Quotient.sound
      (FinitePMF.Equivalent.bind equivalent fun value => FinitePMF.Equivalent.refl
        (kernel value).representative))
    law

theorem bind_ofPMF {α : Type u} {β : Type v} (law : FinitePMF α)
    (kernel : α → FiniteDistribution β) :
    bind (ofPMF law) kernel =
      ofPMF (law.bind fun value => (kernel value).representative) :=
  rfl

theorem representative_pure_equivalent {α : Type u} (value : α) :
    (pure value).representative ≈ₚ FinitePMF.dirac value :=
  representative_equivalent (pure value) (FinitePMF.dirac value) rfl

theorem representative_bind_equivalent {α : Type u} {β : Type v}
    (law : FiniteDistribution α) (kernel : α → FiniteDistribution β) :
    (bind law kernel).representative ≈ₚ
      law.representative.bind fun value => (kernel value).representative := by
  have equal : ofPMF (bind law kernel).representative =
      ofPMF (law.representative.bind fun value => (kernel value).representative) := calc
    ofPMF (bind law kernel).representative = bind law kernel :=
      ofPMF_representative _
    _ = bind (ofPMF law.representative) kernel := by
      rw [ofPMF_representative]
    _ = ofPMF (law.representative.bind fun value =>
        (kernel value).representative) := bind_ofPMF _ _
  exact @Quotient.exact (FinitePMF β) (FinitePMF.equivalentSetoid β)
    (bind law kernel).representative
    (law.representative.bind fun value => (kernel value).representative) equal

theorem bind_pure_left {α : Type u} {β : Type v} (value : α)
    (kernel : α → FiniteDistribution β) :
    bind (pure value) kernel = kernel value := by
  calc
    bind (pure value) kernel =
        ofPMF ((FinitePMF.dirac value).bind fun input =>
          (kernel input).representative) := rfl
    _ = ofPMF (kernel value).representative :=
      Quotient.sound (FinitePMF.bind_dirac_left value fun input =>
        (kernel input).representative)
    _ = kernel value := ofPMF_representative _

theorem bind_pure_right {α : Type u} (law : FiniteDistribution α) :
    bind law pure = law := by
  refine Quotient.inductionOn law ?_
  intro representative
  change ofPMF (representative.bind fun value => (pure value).representative) =
    ofPMF representative
  apply Quotient.sound
  exact FinitePMF.Equivalent.trans
    (FinitePMF.Equivalent.bind (FinitePMF.Equivalent.refl representative)
      representative_pure_equivalent)
    (FinitePMF.bind_dirac_right representative)

theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (law : FiniteDistribution α) (first : α → FiniteDistribution β)
    (second : β → FiniteDistribution γ) :
    bind (bind law first) second =
      bind law fun value => bind (first value) second := by
  refine Quotient.inductionOn law ?_
  intro representative
  change ofPMF ((representative.bind fun value => (first value).representative).bind
      fun value => (second value).representative) =
    ofPMF (representative.bind fun value =>
      (bind (first value) second).representative)
  apply Quotient.sound
  exact FinitePMF.Equivalent.trans
    (FinitePMF.bind_assoc representative
      (fun value => (first value).representative)
      (fun value => (second value).representative))
    (FinitePMF.Equivalent.bind (FinitePMF.Equivalent.refl representative)
      fun value => (representative_bind_equivalent (first value) second).symm)

theorem map_id {α : Type u} (law : FiniteDistribution α) :
    map (fun value => value) law = law := by
  refine Quotient.inductionOn law ?_
  intro representative
  exact Quotient.sound (FinitePMF.map_id representative)

theorem map_comp {α : Type u} {β : Type v} {γ : Type w}
    (first : α → β) (second : β → γ) (law : FiniteDistribution α) :
    map second (map first law) = map (fun value => second (first value)) law := by
  refine Quotient.inductionOn law ?_
  intro representative
  exact Quotient.sound (FinitePMF.map_comp first second representative)

theorem map_pure {α : Type u} {β : Type v} (transform : α → β) (value : α) :
    map transform (pure value) = pure (transform value) := by
  apply Quotient.sound
  intro integrand
  rfl

theorem bind_congr {α : Type u} {β : Type v}
    (law : FiniteDistribution α) {left right : α → FiniteDistribution β}
    (equal : ∀ value, left value = right value) :
    bind law left = bind law right := by
  have kernelsEqual : left = right := funext equal
  subst kernelsEqual
  rfl

theorem map_eq_bind_pure {α : Type u} {β : Type v}
    (transform : α → β) (law : FiniteDistribution α) :
    map transform law = bind law (fun value => pure (transform value)) := by
  refine Quotient.inductionOn law ?_
  intro representative
  change ofPMF (representative.map transform) =
    ofPMF (representative.bind fun value => (pure (transform value)).representative)
  apply Quotient.sound
  exact FinitePMF.Equivalent.symm (FinitePMF.Equivalent.trans
    (FinitePMF.Equivalent.bind (FinitePMF.Equivalent.refl representative)
      fun value => representative_pure_equivalent (transform value))
    (FinitePMF.bind_dirac_map representative transform))

theorem bind_map_left {α : Type u} {β : Type v} {γ : Type w}
    (transform : α → β) (law : FiniteDistribution α)
    (kernel : β → FiniteDistribution γ) :
    bind (map transform law) kernel = bind law (fun value => kernel (transform value)) := by
  rw [map_eq_bind_pure, bind_assoc]
  apply bind_congr
  intro value
  exact bind_pure_left (transform value) kernel

theorem bind_map_right {α : Type u} {β : Type v} {γ : Type w}
    (law : FiniteDistribution α) (kernel : α → FiniteDistribution β)
    (transform : β → γ) :
    bind law (fun value => map transform (kernel value)) =
      map transform (bind law kernel) := by
  calc
    bind law (fun value => map transform (kernel value)) =
        bind law (fun value => bind (kernel value) fun result =>
          pure (transform result)) := by
      apply bind_congr
      intro value
      exact map_eq_bind_pure transform (kernel value)
    _ = bind (bind law kernel) (fun result => pure (transform result)) :=
      (bind_assoc law kernel fun result => pure (transform result)).symm
    _ = map transform (bind law kernel) :=
      (map_eq_bind_pure transform (bind law kernel)).symm

theorem bind_commute {α : Type u} {β : Type v} {γ : Type w}
    (left : FiniteDistribution α) (right : FiniteDistribution β)
    (kernel : α → β → FiniteDistribution γ) :
    bind left (fun leftValue => bind right (kernel leftValue)) =
      bind right (fun rightValue => bind left (fun leftValue =>
        kernel leftValue rightValue)) := by
  refine Quotient.inductionOn left ?_
  intro leftRepresentative
  refine Quotient.inductionOn right ?_
  intro rightRepresentative
  change ofPMF (leftRepresentative.bind fun leftValue =>
      (bind (ofPMF rightRepresentative) (kernel leftValue)).representative) =
    ofPMF (rightRepresentative.bind fun rightValue =>
      (bind (ofPMF leftRepresentative) (fun leftValue =>
        kernel leftValue rightValue)).representative)
  apply Quotient.sound
  have leftNested : ∀ leftValue,
      (bind (ofPMF rightRepresentative) (kernel leftValue)).representative ≈ₚ
        rightRepresentative.bind fun rightValue =>
          (kernel leftValue rightValue).representative := by
    intro leftValue
    exact FinitePMF.Equivalent.trans
      (representative_bind_equivalent (ofPMF rightRepresentative)
        (kernel leftValue))
      (FinitePMF.Equivalent.bind
        (representative_equivalent (ofPMF rightRepresentative)
          rightRepresentative rfl)
        (fun rightValue => FinitePMF.Equivalent.refl
          (kernel leftValue rightValue).representative))
  have rightNested : ∀ rightValue,
      (bind (ofPMF leftRepresentative) (fun leftValue =>
        kernel leftValue rightValue)).representative ≈ₚ
        leftRepresentative.bind fun leftValue =>
          (kernel leftValue rightValue).representative := by
    intro rightValue
    exact FinitePMF.Equivalent.trans
      (representative_bind_equivalent (ofPMF leftRepresentative)
        (fun leftValue => kernel leftValue rightValue))
      (FinitePMF.Equivalent.bind
        (representative_equivalent (ofPMF leftRepresentative)
          leftRepresentative rfl)
        (fun leftValue => FinitePMF.Equivalent.refl
          (kernel leftValue rightValue).representative))
  exact FinitePMF.Equivalent.trans
    (FinitePMF.Equivalent.bind (FinitePMF.Equivalent.refl leftRepresentative)
      leftNested)
    (FinitePMF.Equivalent.trans
      (FinitePMF.bind_commute leftRepresentative rightRepresentative
        fun leftValue rightValue => (kernel leftValue rightValue).representative)
      (FinitePMF.Equivalent.symm
        (FinitePMF.Equivalent.bind (FinitePMF.Equivalent.refl rightRepresentative)
          rightNested)))

end FiniteDistribution

end Foundations.Probability
