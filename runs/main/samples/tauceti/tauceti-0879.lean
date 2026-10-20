public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

theorem infinityPlace.isUniformizer_X_div_mk_Y :
    (infinityPlace W).IsUniformizer (algebraMap W.CoordinateRing W.FunctionField
        (algebraMap F[X] W.CoordinateRing Polynomial.X) /
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      ⟨_, infinityPlace.X_div_mk_Y W⟩]
  exact infinityPlace.X_div_mk_Y W

end WeierstrassCurve.Affine
end
