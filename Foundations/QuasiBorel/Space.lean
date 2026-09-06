module

public import Foundations.QuasiBorel.Source

namespace Foundations.QuasiBorel

public section

universe u v w x

structure Space {Ω : Type u} (source : Source Ω) where
  Carrier : Type v
  Random : (Ω → Carrier) → Prop
  constant : ∀ value, Random (fun _ => value)
  reparam : ∀ {reparam random}, source.Measurable reparam → Random random →
    Random (fun value => random (reparam value))
  piecewise : ∀ {partition : Ω → Nat} {branches : Nat → Ω → Carrier},
    source.Partition partition → (∀ index, Random (branches index)) →
      Random (fun value => branches (partition value) value)

structure Hom {Ω : Type u} {source : Source Ω}
    (domain : Space source) (codomain : Space source) where
  toFun : domain.Carrier → codomain.Carrier
  mapRandom : ∀ {random}, domain.Random random →
    codomain.Random (fun value => toFun (random value))

namespace Hom

instance {Ω : Type u} {source : Source Ω} {domain codomain : Space source} :
    CoeFun (Hom domain codomain) (fun _ => domain.Carrier → codomain.Carrier) where
  coe := Hom.toFun

@[ext] theorem ext {Ω : Type u} {source : Source Ω} {domain codomain : Space source}
    {left right : Hom domain codomain} (equal : ∀ value, left value = right value) :
    left = right := by
  cases left with
  | mk leftFunction leftRandom =>
      cases right with
      | mk rightFunction rightRandom =>
          simp only at equal
          have functionsEqual : leftFunction = rightFunction := funext equal
          cases functionsEqual
          rfl

@[expose] def identity {Ω : Type u} {source : Source Ω} (space : Space source) : Hom space space where
  toFun := fun value => value
  mapRandom := fun random => random

@[expose] def comp {Ω : Type u} {source : Source Ω} {first second third : Space source}
    (after : Hom second third) (before : Hom first second) : Hom first third where
  toFun := fun value => after (before value)
  mapRandom := fun random => after.mapRandom (before.mapRandom random)

@[simp] theorem identity_apply {Ω : Type u} {source : Source Ω} (space : Space source)
    (value : space.Carrier) : identity space value = value := rfl

@[simp] theorem comp_apply {Ω : Type u} {source : Source Ω}
    {first second third : Space source} (after : Hom second third) (before : Hom first second)
    (value : first.Carrier) : comp after before value = after (before value) := rfl

theorem identity_left {Ω : Type u} {source : Source Ω} {domain codomain : Space source}
    (morphism : Hom domain codomain) : comp (identity codomain) morphism = morphism := by
  ext value
  rfl

theorem identity_right {Ω : Type u} {source : Source Ω} {domain codomain : Space source}
    (morphism : Hom domain codomain) : comp morphism (identity domain) = morphism := by
  ext value
  rfl

theorem comp_assoc {Ω : Type u} {source : Source Ω}
    {first second third fourth : Space source}
    (thirdMap : Hom third fourth) (secondMap : Hom second third) (firstMap : Hom first second) :
    comp (comp thirdMap secondMap) firstMap = comp thirdMap (comp secondMap firstMap) := by
  ext value
  rfl

end Hom

namespace Space

@[reducible, expose] def unrestricted {Ω : Type u} (source : Source Ω) (Carrier : Type v) : Space source where
  Carrier := Carrier
  Random := fun _ => True
  constant := fun _ => True.intro
  reparam := fun _ _ => True.intro
  piecewise := fun _ _ => True.intro

@[expose] def sourceObject {Ω : Type u} (source : Source Ω) : Space source where
  Carrier := Ω
  Random := source.Measurable
  constant := source.constant
  reparam := fun outer inner => source.comp outer inner
  piecewise := fun partition branches => source.piecewise partition branches

@[expose] def terminal {Ω : Type u} (source : Source Ω) : Space source where
  Carrier := Unit
  Random := fun _ => True
  constant := fun _ => True.intro
  reparam := fun _ _ => True.intro
  piecewise := fun _ _ => True.intro

@[expose] def terminate {Ω : Type u} {source : Source Ω} (space : Space source) :
    Hom space (terminal source) where
  toFun := fun _ => ()
  mapRandom := fun _ => True.intro

theorem terminate_unique {Ω : Type u} {source : Source Ω} {space : Space source}
    (morphism : Hom space (terminal source)) : morphism = terminate space := by
  ext value
  cases morphism value
  rfl

@[expose] def product {Ω : Type u} {source : Source Ω} (left right : Space source) : Space source where
  Carrier := left.Carrier × right.Carrier
  Random := fun random =>
    left.Random (fun value => (random value).1) ∧
      right.Random (fun value => (random value).2)
  constant := fun value => ⟨left.constant value.1, right.constant value.2⟩
  reparam := by
    intro reparam random reparamMeasurable randomMeasurable
    exact ⟨left.reparam reparamMeasurable randomMeasurable.1,
      right.reparam reparamMeasurable randomMeasurable.2⟩
  piecewise := by
    intro partition branches partitionMeasurable branchesRandom
    exact ⟨left.piecewise partitionMeasurable
        (fun index => (branchesRandom index).1),
      right.piecewise partitionMeasurable
        (fun index => (branchesRandom index).2)⟩

@[expose] def first {Ω : Type u} {source : Source Ω} (left right : Space source) :
    Hom (product left right) left where
  toFun := Prod.fst
  mapRandom := fun random => random.1

@[expose] def second {Ω : Type u} {source : Source Ω} (left right : Space source) :
    Hom (product left right) right where
  toFun := Prod.snd
  mapRandom := fun random => random.2

@[expose] def pair {Ω : Type u} {source : Source Ω} {domain left right : Space source}
    (leftMap : Hom domain left) (rightMap : Hom domain right) :
    Hom domain (product left right) where
  toFun := fun value => (leftMap value, rightMap value)
  mapRandom := fun random => ⟨leftMap.mapRandom random, rightMap.mapRandom random⟩

@[simp] theorem first_pair {Ω : Type u} {source : Source Ω}
    {domain left right : Space source} (leftMap : Hom domain left) (rightMap : Hom domain right) :
    Hom.comp (first left right) (pair leftMap rightMap) = leftMap := by
  ext value
  rfl

@[simp] theorem second_pair {Ω : Type u} {source : Source Ω}
    {domain left right : Space source} (leftMap : Hom domain left) (rightMap : Hom domain right) :
    Hom.comp (second left right) (pair leftMap rightMap) = rightMap := by
  ext value
  rfl

theorem pair_unique {Ω : Type u} {source : Source Ω}
    {domain left right : Space source} (morphism : Hom domain (product left right)) :
    pair (Hom.comp (first left right) morphism) (Hom.comp (second left right) morphism) =
      morphism := by
  ext value
  rfl

end Space

end

end Foundations.QuasiBorel
