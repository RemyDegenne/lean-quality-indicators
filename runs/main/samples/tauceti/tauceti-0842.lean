public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uB uM uP

section LeftModule

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  (m : P → P → B) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]

theorem twistedDifferential_smul (hM : IsDGBimodule hA hB ℳ dM) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p)
    (f : P → M) :
    twistedDifferential m ℳ dM (a • f) =
      dA a • f + p.negOnePow • (a • twistedDifferential m ℳ dM f) := by
  classical
  -- Both sides are additive in `f`; reduce to the homogeneous elementary tensors `α ⊗ x`.
  rw [← Finset.univ_sum_single f, Finset.smul_sum, map_sum, Finset.smul_sum, map_sum,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  generalize f x = α
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i α => exact twistedDifferential_smul_single m dM hM ha x α.2
  | add α β hα hβ =>
    rw [Pi.single_add, smul_add, map_add, hα, hβ, smul_add, map_add, smul_add, smul_add]
    abel

end LeftModule
end TauCeti
end
