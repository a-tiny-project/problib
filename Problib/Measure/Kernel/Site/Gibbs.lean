module

public import Problib.Measure.Kernel.Site
public import Problib.Measure.Kernel.Density.Conditional
public import Problib.Algebra.Product
import Problib.Measure.Extended.Algebra.Binary
import Problib.Measure.Integral.Density.Algebra

/-! Gibbs updates of factor graphs on dependent products.

A factor reads the sites of its scope through a measurable potential, and the
joint density of a list of factors is the product of their potentials. The
Gibbs conditional at a site normalizes the joint density along the line through
the point in that coordinate, against a reference measure for the site. When
every factor whose scope omits the site is finite and nonzero, the conditional
reads only the blanket of the site, the other sites of the factors that mention
it. Gibbs updates at sites that share no factor then commute, and a scan over
sites that pairwise share no factor is the same kernel in every order.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Site

open Problib.Real

universe u v w

variable {ι : Type u} {α : ι → Type v} {spaces : ∀ index, Space (α index)}

/-- A factor of a joint density: a measurable potential that reads only the
sites of its scope. -/
public structure Factor (spaces : ∀ index, Space (α index)) where
  scope : Set ι
  potential : (∀ index, α index) → ENNReal
  measurable : ENNRealMeasurable (Space.pi spaces) potential
  reads : Reads potential scope

/-- A factor that reads one site through a measurable function of its
coordinate. -/
@[expose] public def Factor.unary (site : ι) (potential : α site → ENNReal)
    (measurable : ENNRealMeasurable (spaces site) potential) : Factor spaces where
  scope := fun index => index = site
  potential := fun point => potential (point site)
  measurable := ENNRealMeasurable.comp measurable (Space.coordinate_measurable spaces site)
  reads := fun _ _ agree => congrArg potential (agree site rfl)

/-- The potential is finite and nonzero at every point. -/
@[expose] public def Factor.Positive (factor : Factor spaces) : Prop :=
  ∀ point, ENNReal.Finite (factor.potential point) ∧ factor.potential point ≠ ENNReal.zero

/-- The joint density of a list of factors: the product of their potentials. -/
@[expose] public noncomputable def joint (factors : List (Factor spaces))
    (point : ∀ index, α index) : ENNReal :=
  ENNReal.multiplicativeLaws.listProduct (factors.map fun factor => factor.potential point)

public theorem joint_measurable :
    ∀ factors : List (Factor spaces), ENNRealMeasurable (Space.pi spaces) (joint factors)
  | [] => ENNRealMeasurable.constant _ ENNReal.one
  | factor :: rest => ENNRealMeasurable.mul factor.measurable (joint_measurable rest)

/-- The sites other than `site` that share a factor with `site`. -/
@[expose] public def blanket (factors : List (Factor spaces)) (site : ι) : Set ι :=
  fun index => index ≠ site ∧
    ∃ factor, factor ∈ factors ∧ factor.scope site ∧ factor.scope index

open Classical in
/-- The product of the factors whose scope contains `site`. -/
private noncomputable def adjacent (site : ι) :
    List (Factor spaces) → (∀ index, α index) → ENNReal
  | [] => fun _ => ENNReal.one
  | factor :: rest => fun point =>
      if factor.scope site then ENNReal.mul (factor.potential point) (adjacent site rest point)
      else adjacent site rest point

open Classical in
/-- The product of the factors whose scope omits `site`. -/
private noncomputable def away (site : ι) :
    List (Factor spaces) → (∀ index, α index) → ENNReal
  | [] => fun _ => ENNReal.one
  | factor :: rest => fun point =>
      if factor.scope site then away site rest point
      else ENNReal.mul (factor.potential point) (away site rest point)

private theorem adjacent_of_scope {site : ι} {factor : Factor spaces}
    (rest : List (Factor spaces)) (mentions : factor.scope site) (point : ∀ index, α index) :
    adjacent site (factor :: rest) point =
      ENNReal.mul (factor.potential point) (adjacent site rest point) :=
  ite_eq_left mentions

private theorem adjacent_of_not_scope {site : ι} {factor : Factor spaces}
    (rest : List (Factor spaces)) (absent : ¬factor.scope site) (point : ∀ index, α index) :
    adjacent site (factor :: rest) point = adjacent site rest point :=
  ite_eq_right absent

private theorem away_of_scope {site : ι} {factor : Factor spaces}
    (rest : List (Factor spaces)) (mentions : factor.scope site) (point : ∀ index, α index) :
    away site (factor :: rest) point = away site rest point :=
  ite_eq_left mentions

private theorem away_of_not_scope {site : ι} {factor : Factor spaces}
    (rest : List (Factor spaces)) (absent : ¬factor.scope site) (point : ∀ index, α index) :
    away site (factor :: rest) point =
      ENNReal.mul (factor.potential point) (away site rest point) :=
  ite_eq_right absent

private theorem adjacent_measurable (site : ι) :
    ∀ factors : List (Factor spaces), ENNRealMeasurable (Space.pi spaces) (adjacent site factors)
  | [] => ENNRealMeasurable.constant _ ENNReal.one
  | factor :: rest => by
      classical
      by_cases mentions : factor.scope site
      · rw [show adjacent site (factor :: rest) = fun point =>
            ENNReal.mul (factor.potential point) (adjacent site rest point) from
          funext (adjacent_of_scope rest mentions)]
        exact ENNRealMeasurable.mul factor.measurable (adjacent_measurable site rest)
      · rw [show adjacent site (factor :: rest) = adjacent site rest from
          funext (adjacent_of_not_scope rest mentions)]
        exact adjacent_measurable site rest

/-- The joint density splits into the factors away from `site` times the
factors that mention it. -/
private theorem joint_eq_mul (site : ι) :
    ∀ (factors : List (Factor spaces)) (point : ∀ index, α index),
      joint factors point = ENNReal.mul (away site factors point) (adjacent site factors point)
  | [], _ => (ENNReal.one_mul ENNReal.one).symm
  | factor :: rest, point => by
      classical
      show ENNReal.mul (factor.potential point) (joint rest point) = _
      rw [joint_eq_mul site rest point]
      by_cases mentions : factor.scope site
      · rw [away_of_scope rest mentions, adjacent_of_scope rest mentions, ← ENNReal.mul_assoc,
          ENNReal.mul_comm (factor.potential point) (away site rest point), ENNReal.mul_assoc]
      · rw [away_of_not_scope rest mentions, adjacent_of_not_scope rest mentions,
          ENNReal.mul_assoc]

/-- The factors away from `site` are finite and nonzero when each of them is
positive. -/
private theorem away_bounds (site : ι) :
    ∀ factors : List (Factor spaces),
      (∀ factor, factor ∈ factors → ¬factor.scope site → factor.Positive) →
      ∀ point, ENNReal.Finite (away site factors point) ∧ away site factors point ≠ ENNReal.zero
  | [], _, _ => ⟨True.intro, ENNReal.one_ne_zero⟩
  | factor :: rest, positive, point => by
      classical
      have bounds := away_bounds site rest
        (fun other member => positive other (List.mem_cons_of_mem factor member)) point
      by_cases mentions : factor.scope site
      · rw [away_of_scope rest mentions]
        exact bounds
      · rw [away_of_not_scope rest mentions]
        have factorBounds := positive factor List.mem_cons_self mentions point
        refine ⟨ENNReal.mul_finite factorBounds.1 bounds.1, ?_⟩
        intro null
        rcases ENNReal.mul_eq_zero_iff.mp null with factorZero | restZero
        · exact factorBounds.2 factorZero
        · exact bounds.2 restZero

/-- The factors that mention `site` agree at two points that agree on every
site those factors read. -/
private theorem adjacent_congr (site : ι) :
    ∀ (factors : List (Factor spaces)) (first second : ∀ index, α index),
      (∀ factor, factor ∈ factors → factor.scope site →
        ∀ index, factor.scope index → first index = second index) →
      adjacent site factors first = adjacent site factors second
  | [], _, _, _ => rfl
  | factor :: rest, first, second, agree => by
      classical
      have restEqual := adjacent_congr site rest first second
        (fun other member => agree other (List.mem_cons_of_mem factor member))
      by_cases mentions : factor.scope site
      · rw [adjacent_of_scope rest mentions, adjacent_of_scope rest mentions,
          factor.reads first second (agree factor List.mem_cons_self mentions), restEqual]
      · rw [adjacent_of_not_scope rest mentions, adjacent_of_not_scope rest mentions, restEqual]

/-- A conditional kernel whose density is a finite, nonzero weight of the input
times a remainder that reads only `sites` reads only `sites`. -/
public theorem densityConditional_reads {β : Type w} {target : Space β}
    (reference : Measure target) (referenceFinite : Measure.SFinite reference)
    {density : (∀ index, α index) → β → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product (Space.pi spaces) target)
      (fun pair => density pair.1 pair.2))
    (fallback : β) {weight : (∀ index, α index) → ENNReal}
    {remainder : (∀ index, α index) → β → ENNReal}
    (remainderMeasurable : ENNRealMeasurable (Space.product (Space.pi spaces) target)
      (fun pair => remainder pair.1 pair.2))
    (split : ∀ point value,
      density point value = ENNReal.mul (weight point) (remainder point value))
    (weightFinite : ∀ point, ENNReal.Finite (weight point))
    (weightNonzero : ∀ point, weight point ≠ ENNReal.zero)
    {sites : Set ι} (remainderReads : Reads remainder sites) :
    Reads (densityConditional reference referenceFinite density densityMeasurable fallback)
      sites := by
  have equal : density = fun point value => ENNReal.mul (weight point) (remainder point value) :=
    funext (fun point => funext (split point))
  subst equal
  intro first second agree
  rw [densityConditional_mul_left reference referenceFinite remainderMeasurable
      densityMeasurable fallback first (weightFinite first) (weightNonzero first),
    densityConditional_mul_left reference referenceFinite remainderMeasurable
      densityMeasurable fallback second (weightFinite second) (weightNonzero second)]
  exact densityConditional_congr_fiber reference referenceFinite remainderMeasurable fallback
    (remainderReads first second agree)

variable [DecidableEq ι]

/-- The factors away from `site` do not read `site`. -/
private theorem away_replace (site : ι) :
    ∀ (factors : List (Factor spaces)) (point : ∀ index, α index) (value : α site),
      away site factors (replace point site value) = away site factors point
  | [], _, _ => rfl
  | factor :: rest, point, value => by
      classical
      by_cases mentions : factor.scope site
      · rw [away_of_scope rest mentions, away_of_scope rest mentions,
          away_replace site rest point value]
      · rw [away_of_not_scope rest mentions, away_of_not_scope rest mentions,
          away_replace site rest point value,
          factor.reads (replace point site value) point
            (fun index inScope => replace_of_ne point value
              (fun equal => mentions (equal ▸ inScope)))]

private theorem joint_replace (site : ι) (factors : List (Factor spaces))
    (point : ∀ index, α index) (value : α site) :
    joint factors (replace point site value) =
      ENNReal.mul (away site factors point) (adjacent site factors (replace point site value)) := by
  rw [joint_eq_mul site factors, away_replace]

/-- Along the line through a point in coordinate `site`, the factors that
mention `site` read only the blanket of `site`. -/
private theorem adjacent_line_reads (site : ι) (factors : List (Factor spaces)) :
    Reads (fun point value => adjacent site factors (replace point site value))
      (blanket factors site) := by
  intro first second agree
  funext value
  apply adjacent_congr site factors
  intro factor member mentions index inScope
  by_cases atSite : index = site
  · subst atSite
    rw [replace_same, replace_same]
  · rw [replace_of_ne first value atSite, replace_of_ne second value atSite]
    exact agree index ⟨atSite, factor, member, mentions, inScope⟩

/-- The Gibbs conditional at `site`: the joint density along the line through
the point in coordinate `site`, normalized against the reference measure of the
site. A line of zero or infinite mass takes the Dirac measure at the fallback
value of the site. -/
@[expose] public noncomputable def conditional (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) : Kernel (Space.pi spaces) (spaces site) :=
  densityConditional (reference site) (referenceFinite site)
    (fun point value => joint factors (replace point site value))
    (ENNRealMeasurable.comp (joint_measurable factors) (replace_measurable site))
    (fallback site)

/-- The Gibbs update at `site` as a sweep step. -/
@[expose, implicit_reducible] public noncomputable def gibbsStep (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) : Step spaces where
  site := site
  kernel := conditional factors reference referenceFinite fallback site
  finite := (densityConditional_isFinite (reference site) (referenceFinite site) _
    (fallback site)).toSFinite

/-- Every Gibbs conditional is a probability kernel. -/
public theorem conditional_isProbability (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) (point : ∀ index, α index) :
    Measure.IsProbability (conditional factors reference referenceFinite fallback site point) :=
  densityConditional_isProbability (reference site) (referenceFinite site) _ (fallback site) point

public theorem gibbsStep_run_apply (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) (point : ∀ index, α index) :
    (gibbsStep factors reference referenceFinite fallback site).run point =
      (conditional factors reference referenceFinite fallback site point).map
        (replace point site) (replace_value_measurable point site) :=
  update_apply site _ _ point

/-- The Gibbs conditional at a site does not read the site. -/
public theorem conditional_ignores (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) :
    Ignores (conditional factors reference referenceFinite fallback site) site := by
  intro point value
  unfold conditional
  apply densityConditional_congr_fiber
  funext other
  exact congrArg (joint factors) (replace_replace_same point site value other)

/-- The Gibbs conditional keeps `lower / upper` of a probability reference at
its site when the joint density lies between `lower > 0` and `upper`. -/
public theorem conditional_lower (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (fallback : ∀ index, α index) (site : ι) {lower upper : NNReal}
    (lowerPositive : NNReal.lt NNReal.zero lower)
    (bounded : ∀ point, ENNReal.le (ENNReal.finite lower) (joint factors point) ∧
      ENNReal.le (joint factors point) (ENNReal.finite upper))
    (point : ∀ index, α index) {set : Set (α site)}
    (setMeasurable : (spaces site).Measurable set) :
    ENNReal.le (ENNReal.mul (ENNReal.finite (NNReal.div lower upper)) (reference site set))
      (conditional factors reference referenceFinite fallback site point set) :=
  densityConditional_lower (reference site) (referenceFinite site) (referenceProbability site) _
    (fallback site) lowerPositive (fun point value => bounded (replace point site value)) point
    setMeasurable

/-- The Gibbs conditional at `site` reads only the blanket of `site` when every
factor whose scope omits `site` is finite and nonzero. -/
public theorem conditional_reads_blanket (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι)
    (positive : ∀ factor, factor ∈ factors → ¬factor.scope site → factor.Positive) :
    Reads (conditional factors reference referenceFinite fallback site)
      (blanket factors site) :=
  densityConditional_reads (reference site) (referenceFinite site) _ (fallback site)
    (weight := away site factors)
    (remainder := fun point value => adjacent site factors (replace point site value))
    (ENNRealMeasurable.comp (adjacent_measurable site factors) (replace_measurable site))
    (joint_replace site factors)
    (fun point => (away_bounds site factors positive point).1)
    (fun point => (away_bounds site factors positive point).2)
    (adjacent_line_reads site factors)

/-- Gibbs steps at distinct sites that share no factor are independent when
every factor whose scope omits either site is finite and nonzero. -/
public theorem gibbsStep_independent (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) {first second : ι} (distinct : first ≠ second)
    (separate : ∀ factor, factor ∈ factors → factor.scope first → ¬factor.scope second)
    (firstPositive : ∀ factor, factor ∈ factors → ¬factor.scope first → factor.Positive)
    (secondPositive : ∀ factor, factor ∈ factors → ¬factor.scope second → factor.Positive) :
    Independent (gibbsStep factors reference referenceFinite fallback first)
      (gibbsStep factors reference referenceFinite fallback second) := by
  refine ⟨distinct, ?_, ?_⟩
  · apply ignores_of_reads (conditional_reads_blanket factors reference referenceFinite
      fallback first firstPositive)
    intro inBlanket
    obtain ⟨_, factor, member, mentionsFirst, mentionsSecond⟩ := inBlanket
    exact separate factor member mentionsFirst mentionsSecond
  · apply ignores_of_reads (conditional_reads_blanket factors reference referenceFinite
      fallback second secondPositive)
    intro inBlanket
    obtain ⟨_, factor, member, mentionsSecond, mentionsFirst⟩ := inBlanket
    exact separate factor member mentionsFirst mentionsSecond

/-- Gibbs updates at distinct sites that share no factor commute when every
factor whose scope omits either site is finite and nonzero. -/
public theorem gibbs_comm (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) {first second : ι} (distinct : first ≠ second)
    (separate : ∀ factor, factor ∈ factors → factor.scope first → ¬factor.scope second)
    (firstPositive : ∀ factor, factor ∈ factors → ¬factor.scope first → factor.Positive)
    (secondPositive : ∀ factor, factor ∈ factors → ¬factor.scope second → factor.Positive) :
    (gibbsStep factors reference referenceFinite fallback first).run.comp
        (gibbsStep factors reference referenceFinite fallback second).run =
      (gibbsStep factors reference referenceFinite fallback second).run.comp
        (gibbsStep factors reference referenceFinite fallback first).run :=
  Step.run_comm (gibbsStep_independent factors reference referenceFinite fallback distinct
    separate firstPositive secondPositive)

/-- A Gibbs scan over sites that pairwise share no factor is the same kernel in
every order, when every factor whose scope omits a scanned site is finite and
nonzero. -/
public theorem gibbs_sweep_perm (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) {first second : List ι} (perm : first.Perm second)
    (separate : first.Pairwise (fun one other => one ≠ other ∧
      ∀ factor, factor ∈ factors → factor.scope one → ¬factor.scope other))
    (positive : ∀ site, site ∈ first →
      ∀ factor, factor ∈ factors → ¬factor.scope site → factor.Positive) :
    sweep (first.map (gibbsStep factors reference referenceFinite fallback)) =
      sweep (second.map (gibbsStep factors reference referenceFinite fallback)) := by
  apply sweep_perm (perm.map _)
  apply List.pairwise_map.mpr
  apply separate.imp_of_mem
  intro one other oneMember otherMember apart
  exact gibbsStep_independent factors reference referenceFinite fallback apart.1 apart.2
    (positive one oneMember) (positive other otherMember)

/-- `conditional_reads_blanket` needs every factor away from the site to be
positive. On two bits with one factor on the second bit that vanishes at zero,
the first bit has an empty blanket. Against a Dirac reference at one with
fallback zero, its Gibbs conditional is the Dirac measure at one where the
second bit is one and the Dirac measure at zero where it is zero. -/
public theorem vanishing_factor_does_not_localize :
    ¬Reads
      (conditional
        [Factor.unary (spaces := fun _ : Bool => Space.discrete Bool) true
          (fun bit : Bool => if bit then ENNReal.one else ENNReal.zero) (fun _ => True.intro)]
        (fun _ => Measure.dirac (Space.discrete Bool) true)
        (fun _ => Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ true))
        (fun _ => false) false)
      (blanket
        [Factor.unary (spaces := fun _ : Bool => Space.discrete Bool) true
          (fun bit : Bool => if bit then ENNReal.one else ENNReal.zero) (fun _ => True.intro)]
        false) := by
  intro reads
  generalize factorDef : Factor.unary (spaces := fun _ : Bool => Space.discrete Bool) true
    (fun bit : Bool => if bit then ENNReal.one else ENNReal.zero) (fun _ => True.intro) =
      factor at reads
  have scope : factor.scope = fun index => index = true := by
    rw [← factorDef]
    rfl
  have potential : ∀ point : Bool → Bool,
      factor.potential point = if point true then ENNReal.one else ENNReal.zero := by
    intro point
    rw [← factorDef]
    rfl
  have line : ∀ (point : Bool → Bool) (value : Bool),
      joint [factor] (replace point false value) =
        if point true then ENNReal.one else ENNReal.zero := by
    intro point value
    show ENNReal.mul (factor.potential (replace point false value)) ENNReal.one = _
    rw [ENNReal.mul_one, potential,
      replace_of_ne point value (show true ≠ false by decide)]
  have fiberOne : densityFiber (Measure.dirac (Space.discrete Bool) true)
      (fun (point : Bool → Bool) (value : Bool) => joint [factor] (replace point false value))
      (fun _ => true) = Measure.dirac (Space.discrete Bool) true := by
    show (Measure.dirac (Space.discrete Bool) true).withDensity
      (fun value => joint [factor] (replace (fun _ : Bool => true) false value)) = _
    rw [show (fun value : Bool => joint [factor] (replace (fun _ : Bool => true) false value)) =
        fun _ => ENNReal.one from funext (fun value => (line _ value).trans (ite_eq_left rfl))]
    exact Measure.withDensity_one _
  have fiberZero : densityFiber (Measure.dirac (Space.discrete Bool) true)
      (fun (point : Bool → Bool) (value : Bool) => joint [factor] (replace point false value))
      (fun _ => false) = Measure.zero (Space.discrete Bool) := by
    show (Measure.dirac (Space.discrete Bool) true).withDensity
      (fun value => joint [factor] (replace (fun _ : Bool => false) false value)) = _
    rw [show (fun value : Bool => joint [factor] (replace (fun _ : Bool => false) false value)) =
        fun _ => ENNReal.zero from funext (fun value => (line _ value).trans (ite_eq_right (by decide)))]
    exact Measure.withDensity_zero _
  have defined : Measure.IsNormalizable (densityFiber (Measure.dirac (Space.discrete Bool) true)
      (fun (point : Bool → Bool) (value : Bool) => joint [factor] (replace point false value))
      (fun _ => true)) := by
    rw [fiberOne]
    exact (Measure.IsProbability.dirac _ true).to_normalizable
  have undefined : ¬Measure.IsNormalizable (densityFiber
      (Measure.dirac (Space.discrete Bool) true)
      (fun (point : Bool → Bool) (value : Bool) => joint [factor] (replace point false value))
      (fun _ => false)) := by
    rw [fiberZero]
    intro zeroDefined
    exact zeroDefined.nonzero (Measure.zero_apply Set.univ)
  have normalized : Measure.normalize (densityFiber (Measure.dirac (Space.discrete Bool) true)
      (fun (point : Bool → Bool) (value : Bool) => joint [factor] (replace point false value))
      (fun _ => true)) defined = Measure.dirac (Space.discrete Bool) true :=
    Measure.normalize_eq_of_smul_eq _ defined _
      (by rw [fiberOne, Measure.dirac_apply_univ, Measure.one_smul])
  have outside : ∀ index, blanket [factor] false index →
      (fun _ : Bool => true) index = (fun _ : Bool => false) index := by
    intro index inBlanket
    obtain ⟨_, other, member, mentions, _⟩ := inBlanket
    rw [List.mem_singleton] at member
    subst member
    rw [scope] at mentions
    exact absurd mentions (by decide)
  have equal := reads (fun _ => true) (fun _ => false) outside
  unfold conditional at equal
  rw [densityConditional_eq_normalize _ _ _ _ (fun _ => true) defined, normalized,
    densityConditional_eq_dirac _ _ _ _ (fun _ => false) undefined] at equal
  have atOne := congrArg (fun measure : Measure (Space.discrete Bool) =>
    measure (fun bit : Bool => bit = true)) equal
  rw [Measure.dirac_apply_of_mem (set := fun bit : Bool => bit = true) _ _ True.intro rfl,
    Measure.dirac_apply_of_not_mem (set := fun bit : Bool => bit = true) _ _ True.intro
      (by decide)] at atOne
  exact ENNReal.one_ne_zero atOne

end Problib.Measure.Kernel.Site
