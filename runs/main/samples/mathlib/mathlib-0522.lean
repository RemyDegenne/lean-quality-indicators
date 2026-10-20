@[expose] public section

open Algebra Module

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

namespace Algebra.FormallyUnramified

variable [FormallyUnramified R S] [EssFiniteType R S]

lemma one_tmul_mul_elem (s : S) : (1 ⊗ₜ s) * elem R S = (s ⊗ₜ 1) * elem R S := by
  rw [← sub_eq_zero, ← sub_mul, one_tmul_sub_tmul_one_mul_elem]

end Algebra.FormallyUnramified
end
