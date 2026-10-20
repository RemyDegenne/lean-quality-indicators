@[expose] public section

universe u v w

variable {S T : Type*}

variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

namespace QuadraticMap

section CommRing

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (Q : QuadraticMap R M N)

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] [Module S N]
    [IsScalarTower S R N]

@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x, polar_smul_left, algebraMap_smul]

end CommRing
end QuadraticMap
end
