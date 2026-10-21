namespace OAI

section

noncomputable section

open MeasureTheory

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem source_eq_collision (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    source b q F = CollisionCompactness.collisionSource b (density q F) := by
  funext z
  rfl

end BoltzmannNonuniqueness.EuclideanFlight
end
end
end OAI
