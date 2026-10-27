public section

namespace TauCeti

open _root_.Complex Metric Set

open scoped ComplexConjugate

/-- The quantity `R = (1 - ‖a‖ ^ 2) / (2 * |A|)`, with `A = Im (conj u * a)`, read off by
completing the square as in `TauCeti.orthogonalCircleCenter`.

Nothing is asked of `u` or `a` here, so this is a signed algebraic parameter: at `A = 0` the
division is by zero and the value is `0`, and for `A ≠ 0` it is negative for `‖a‖ > 1` (at
`u = 1` and `a = 2 * I` it is `-3/4`). Under `‖a‖ < 1` and `A ≠ 0` it is positive
(`TauCeti.orthogonalCircleRadius_pos`), but it is the radius of the Euclidean circle traced by the
hyperbolic line through `a` in direction `u` only once `‖u‖ = 1` as well
(`TauCeti.setOf_im_eq_ball_inter_sphere`): unlike the centre, `R` is not invariant under
rescaling `u`, because `A` scales with `u` while the numerator does not. -/
noncomputable def orthogonalCircleRadius (u a : ℂ) : ℝ :=
  (1 - ‖a‖ ^ 2) / (2 * |(conj u * a).im|)

end TauCeti
end
