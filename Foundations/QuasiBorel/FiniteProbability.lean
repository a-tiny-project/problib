import Foundations.Probability.Finite.Distribution
import Foundations.QuasiBorel.Space

namespace Foundations.QuasiBorel

open Foundations.Probability

universe u

namespace FiniteProbability

inductive Random {Ω : Type u} {source : Source Ω} (space : Space source) :
    (Ω → FiniteDistribution space.Carrier) → Prop where
  | constant (law : FiniteDistribution space.Carrier) :
      Random space fun _ => law
  | dirac {random : Ω → space.Carrier} (valid : space.Random random) :
      Random space fun sample => FiniteDistribution.pure (random sample)
  | mixture (weights : FiniteDistribution Nat)
      (branches : Nat → Ω → FiniteDistribution space.Carrier)
      (valid : ∀ index, Random space (branches index)) :
      Random space fun sample =>
        FiniteDistribution.bind weights fun index => branches index sample
  | reparam {reparam : Ω → Ω} {random : Ω → FiniteDistribution space.Carrier}
      (reparamValid : source.Measurable reparam) (valid : Random space random) :
      Random space fun sample => random (reparam sample)
  | piecewise {partition : Ω → Nat}
      {branches : Nat → Ω → FiniteDistribution space.Carrier}
      (partitionValid : source.Partition partition)
      (valid : ∀ index, Random space (branches index)) :
      Random space fun sample => branches (partition sample) sample

def object {Ω : Type u} {source : Source Ω} (space : Space source) : Space source where
  Carrier := FiniteDistribution space.Carrier
  Random := Random space
  constant := Random.constant
  reparam := Random.reparam
  piecewise := Random.piecewise

def unit {Ω : Type u} {source : Source Ω} (space : Space source) :
    Hom space (object space) where
  toFun := FiniteDistribution.pure
  mapRandom := Random.dirac

theorem Random.bind {Ω : Type u} {source : Source Ω}
    {domain codomain : Space source}
    (kernel : Hom domain (object codomain))
    {family : Ω → FiniteDistribution domain.Carrier}
    (valid : Random domain family) :
    Random codomain fun sample => FiniteDistribution.bind (family sample) kernel := by
  induction valid with
  | constant law =>
      exact Random.constant _
  | @dirac random randomValid =>
      have mapped := kernel.mapRandom randomValid
      change Random codomain (fun sample => kernel (random sample)) at mapped
      have equal :
          (fun sample => FiniteDistribution.bind
            (FiniteDistribution.pure (random sample)) kernel) =
          (fun sample => kernel (random sample)) := by
        funext sample
        exact FiniteDistribution.bind_pure_left _ kernel
      rw [equal]
      exact mapped
  | mixture weights branches branchesValid ih =>
      have mixed := Random.mixture weights
        (fun index sample => FiniteDistribution.bind (branches index sample) kernel) ih
      have equal :
          (fun sample => FiniteDistribution.bind
            (FiniteDistribution.bind weights fun index => branches index sample) kernel) =
          (fun sample => FiniteDistribution.bind weights fun index =>
            FiniteDistribution.bind (branches index sample) kernel) := by
        funext sample
        exact FiniteDistribution.bind_assoc weights
          (fun index => branches index sample) kernel
      rw [equal]
      exact mixed
  | reparam reparamValid randomValid ih =>
      exact Random.reparam reparamValid ih
  | piecewise partitionValid branchesValid ih =>
      exact Random.piecewise partitionValid ih

noncomputable def extend {Ω : Type u} {source : Source Ω}
    {domain codomain : Space source} (kernel : Hom domain (object codomain)) :
    Hom (object domain) (object codomain) where
  toFun := fun law => FiniteDistribution.bind law kernel
  mapRandom := Random.bind kernel

theorem extend_unit_right {Ω : Type u} {source : Source Ω}
    (space : Space source) :
    extend (unit space) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  exact FiniteDistribution.bind_pure_right law

theorem extend_unit_left {Ω : Type u} {source : Source Ω}
    {domain codomain : Space source} (kernel : Hom domain (object codomain)) :
    Hom.comp (extend kernel) (unit domain) = kernel := by
  apply Hom.ext
  intro value
  exact FiniteDistribution.bind_pure_left value kernel

theorem extend_assoc {Ω : Type u} {source : Source Ω}
    {first second third : Space source}
    (firstKernel : Hom first (object second))
    (secondKernel : Hom second (object third)) :
    Hom.comp (extend secondKernel) (extend firstKernel) =
      extend (Hom.comp (extend secondKernel) firstKernel) := by
  apply Hom.ext
  intro law
  exact FiniteDistribution.bind_assoc law firstKernel secondKernel

end FiniteProbability

end Foundations.QuasiBorel
