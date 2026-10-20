public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

namespace IsDGRightModule

section Grading

theorem iSup_cyclesDeg_eq_top (hM : IsDGRightModule h ℳ dM) :
    ⨆ p : ℤ, hM.cyclesDeg p = ⊤ :=
  (DirectSum.Decomposition.isInternal hM.cyclesDeg).submodule_iSup_eq_top

end Grading
end IsDGRightModule
end TauCeti
end
