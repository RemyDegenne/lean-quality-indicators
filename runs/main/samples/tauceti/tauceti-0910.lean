public section

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module A P] [Module Bᵐᵒᵖ P]
  [IsScalarTower R A P] [IsScalarTower R Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] [SetLike.GradedSMul 𝒜 ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}

namespace DGBimoduleHom

variable {hM : IsDGBimodule hA hB ℳ dM} {hN : IsDGBimodule hA hB 𝒩 dN}
  {hP : IsDGBimodule hA hB ℳP dP}

@[simp]
theorem comp_add (g : DGBimoduleHom hN hP) (f f' : DGBimoduleHom hM hN) :
    g.comp (f + f') = g.comp f + g.comp f' := by
  ext x
  simp

end DGBimoduleHom
end TauCeti
end
