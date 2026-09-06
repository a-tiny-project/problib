import Foundations.QuasiBorel.Space

namespace Foundations.QuasiBorel

universe u

namespace Space

@[reducible] def exponential {Ω : Type u} {source : Source Ω}
    (domain codomain : Space source) : Space source where
  Carrier := Hom domain codomain
  Random := fun family =>
    ∀ {randomPair : Ω → (sourceObject source).Carrier × domain.Carrier},
      (product (sourceObject source) domain).Random randomPair →
        codomain.Random fun value => family (randomPair value).1 (randomPair value).2
  constant := by
    intro morphism randomPair randomPairValid
    exact morphism.mapRandom randomPairValid.2
  reparam := by
    intro reparam family reparamMeasurable familyRandom randomPair randomPairValid
    have transformedPairValid :
        (product (sourceObject source) domain).Random
          (fun value => (reparam (randomPair value).1, (randomPair value).2)) :=
      ⟨source.comp randomPairValid.1 reparamMeasurable, randomPairValid.2⟩
    exact familyRandom transformedPairValid
  piecewise := by
    intro partition branches partitionMeasurable branchesRandom randomPair randomPairValid
    change codomain.Random fun value =>
      branches (partition (randomPair value).1) (randomPair value).1 (randomPair value).2
    exact codomain.piecewise
      (source.partitionReparam partitionMeasurable randomPairValid.1)
      (fun index => branchesRandom index randomPairValid)

def evaluate {Ω : Type u} {source : Source Ω} (domain codomain : Space source) :
    Hom (product (exponential domain codomain) domain) codomain where
  toFun := fun pair => pair.1 pair.2
  mapRandom := by
    intro randomPair randomPairValid
    exact randomPairValid.1
      (randomPair := fun value => (value, (randomPair value).2))
      ⟨source.identity, randomPairValid.2⟩

def curry {Ω : Type u} {source : Source Ω} {parameter domain codomain : Space source}
    (morphism : Hom (product parameter domain) codomain) :
    Hom parameter (exponential domain codomain) where
  toFun := fun parameterValue => {
    toFun := fun domainValue => morphism (parameterValue, domainValue)
    mapRandom := fun domainRandom =>
      morphism.mapRandom ⟨parameter.constant parameterValue, domainRandom⟩
  }
  mapRandom := by
    intro parameterRandom parameterRandomValid randomPair randomPairValid
    apply morphism.mapRandom
    exact ⟨parameter.reparam randomPairValid.1 parameterRandomValid, randomPairValid.2⟩

def uncurry {Ω : Type u} {source : Source Ω} {parameter domain codomain : Space source}
    (morphism : Hom parameter (exponential domain codomain)) :
    Hom (product parameter domain) codomain :=
  Hom.comp (evaluate domain codomain)
    (pair (Hom.comp morphism (first parameter domain)) (second parameter domain))

@[simp] theorem evaluate_pair {Ω : Type u} {source : Source Ω}
    {domain codomain : Space source} (function : Hom domain codomain)
    (argument : domain.Carrier) :
    evaluate domain codomain (function, argument) = function argument := rfl

@[simp] theorem curry_apply {Ω : Type u} {source : Source Ω}
    {parameter domain codomain : Space source}
    (morphism : Hom (product parameter domain) codomain)
    (parameterValue : parameter.Carrier) (domainValue : domain.Carrier) :
    curry morphism parameterValue domainValue = morphism (parameterValue, domainValue) := rfl

@[simp] theorem uncurry_apply {Ω : Type u} {source : Source Ω}
    {parameter domain codomain : Space source}
    (morphism : Hom parameter (exponential domain codomain))
    (value : (product parameter domain).Carrier) :
    uncurry morphism value = morphism value.1 value.2 := rfl

theorem uncurry_curry {Ω : Type u} {source : Source Ω}
    {parameter domain codomain : Space source}
    (morphism : Hom (product parameter domain) codomain) :
    uncurry (curry morphism) = morphism := by
  ext value
  rfl

theorem curry_uncurry {Ω : Type u} {source : Source Ω}
    {parameter domain codomain : Space source}
    (morphism : Hom parameter (exponential domain codomain)) :
    curry (uncurry morphism) = morphism := by
  apply Hom.ext
  intro parameterValue
  apply Hom.ext
  intro domainValue
  rfl

end Space

end Foundations.QuasiBorel
