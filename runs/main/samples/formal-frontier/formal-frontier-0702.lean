public section

noncomputable section

namespace SymmetricAlgebra

universe u v w

variable (K : Type u) [CommRing K] (M : Type v) [AddCommMonoid M] [Module K M]
  (R : Type w) [CommRing R] [Algebra K R]

theorem linearMapMulEquivAlgHom_neg_mul (f : M →ₗ[K] R) :
    linearMapMulEquivAlgHom K M R (.ofAdd (-f)) *
      linearMapMulEquivAlgHom K M R (.ofAdd f) = 1 := by
  rw [← (linearMapMulEquivAlgHom K M R).map_mul]
  simp

end SymmetricAlgebra
end
end
