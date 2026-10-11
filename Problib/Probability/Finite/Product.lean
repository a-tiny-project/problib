import Problib.Probability.Finite.Density

namespace Problib.Probability

universe u v

namespace FiniteMeasure

theorem integral_mul_right {α : Type u} (measure : FiniteMeasure α)
    (integrand : α → NNRat) (constant : NNRat) :
    measure.integral (fun value => integrand value * constant) =
      measure.integral integrand * constant := by
  calc
    measure.integral (fun value => integrand value * constant) =
        measure.integral (fun value => constant * integrand value) := by
          apply integral_congr
          intro value
          exact NNRat.mul_comm _ _
    _ = constant * measure.integral integrand :=
      integral_mul_left measure constant integrand
    _ = measure.integral integrand * constant := NNRat.mul_comm _ _

private theorem mass_product_kernel {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (right : FiniteMeasure β) (leftPoint : α) (rightPoint : β) (value : α) :
    (map (fun rightValue => (value, rightValue)) right).mass (leftPoint, rightPoint) =
      if value = leftPoint then right.mass rightPoint else 0 := by
  by_cases equal : value = leftPoint
  · subst value
    rw [ite_eq_left rfl]
    apply mass_map_injective
    intro first second pairEqual
    exact congrArg Prod.snd pairEqual
  · rw [ite_eq_right equal]
    apply mass_map_no_preimage
    intro rightValue pairEqual
    exact equal (congrArg Prod.fst pairEqual)

theorem mass_product {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (left : FiniteMeasure α) (right : FiniteMeasure β)
    (leftPoint : α) (rightPoint : β) :
    (product left right).mass (leftPoint, rightPoint) =
      left.mass leftPoint * right.mass rightPoint := by
  rw [product, mass_bind]
  calc
    left.integral (fun value =>
        (map (fun rightValue => (value, rightValue)) right).mass (leftPoint, rightPoint)) =
        left.integral (fun value =>
          (if value = leftPoint then 1 else 0) * right.mass rightPoint) := by
            apply integral_congr
            intro value
            rw [mass_product_kernel]
            by_cases equal : value = leftPoint
            · simp [equal]
            · simp [equal]
    _ = left.integral (fun value => if value = leftPoint then 1 else 0) *
        right.mass rightPoint :=
      integral_mul_right left (fun value => if value = leftPoint then 1 else 0)
        (right.mass rightPoint)
    _ = left.mass leftPoint * right.mass rightPoint := by
      rw [← mass_eq_integral_indicator]

theorem product_isDensity {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    {left leftReference : FiniteMeasure α} {right rightReference : FiniteMeasure β}
    {leftDensity : α → NNRat} {rightDensity : β → NNRat}
    (leftCorrect : IsDensity left leftReference leftDensity)
    (rightCorrect : IsDensity right rightReference rightDensity) :
    IsDensity (product left right) (product leftReference rightReference)
      (fun point => leftDensity point.1 * rightDensity point.2) := by
  intro point
  rw [mass_product, mass_product, leftCorrect point.1, rightCorrect point.2]
  exact NNRat.mul_mul_mul_comm _ _ _ _

theorem map_isDensity_of_bijection {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    {measure reference : FiniteMeasure α} {density : α → NNRat}
    (densityCorrect : IsDensity measure reference density)
    (forward : α → β) (inverse : β → α)
    (leftInverse : ∀ value, inverse (forward value) = value)
    (rightInverse : ∀ value, forward (inverse value) = value) :
    IsDensity (map forward measure) (map forward reference)
      (fun value => density (inverse value)) := by
  have forwardInjective : ∀ {left right}, forward left = forward right → left = right := by
    intro left right equal
    calc
      left = inverse (forward left) := (leftInverse left).symm
      _ = inverse (forward right) := congrArg inverse equal
      _ = right := leftInverse right
  intro point
  rw [← rightInverse point]
  rw [mass_map_injective forward forwardInjective]
  rw [mass_map_injective forward forwardInjective]
  simpa [leftInverse] using densityCorrect (inverse point)

end FiniteMeasure

namespace FinitePMF

end FinitePMF

end Problib.Probability
