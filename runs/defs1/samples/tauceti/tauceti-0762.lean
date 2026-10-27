public section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {ind : P → ℤ} [Fintype P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind)

variable [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

/-- The twisted complex `ℳ ⊗ ⟨P⟩` of a twisting cocycle, as a cochain complex of `R`-modules. -/
noncomputable abbrev twistedCochainComplex (hM : IsDGRightModule h ℳ dM) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  TauCeti.twistedCochainComplex m.mem_graded m.twisting hM

end TwistingCocycle
end TauCeti
end
