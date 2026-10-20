public section

open Convex Set Metric

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strictConvex_closedBall` below.

See also `StrictConvexSpace.of_strictConvex_unitClosedBall`. -/
@[mk_iff]
class StrictConvexSpace (𝕜 E : Type*) [NormedField 𝕜] [PartialOrder 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop where
  strictConvex_closedBall : ∀ r : ℝ, 0 < r → StrictConvex 𝕜 (closedBall (0 : E) r)

end
