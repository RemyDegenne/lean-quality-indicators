public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section Bracket

variable [LieGroup I 3 G]

attribute [local instance] LieGroup.minSmoothnessThree

local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := 3) (by norm_num)

/-- The group adjoint automorphism: the differential at the identity of conjugation by `g`. -/
def tangentAd [CompleteSpace E] (g : G) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G where
  toFun := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv
  invFun := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.symm
  left_inv := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.left_inv
  right_inv := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.right_inv
  map_add' := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.map_add
  map_smul' := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.map_smul
  map_lie' := by
    intro X Y
    exact adjointContinuousLinearMap_lie (I := I) g X Y

end Bracket
end TauCeti.Lie
end
end
