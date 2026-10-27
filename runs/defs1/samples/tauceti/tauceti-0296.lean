public section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {ind : P → ℤ} [Fintype P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

section SqZero

variable [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass R Aᵐᵒᵖ M] (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  (dM : M →ₗ[R] M) [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

variable {m dM} (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
  (htw : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
  (hM : IsDGRightModule h ℳ dM)

/-- The twisted complex `ℳ ⊗ ⟨P⟩` of a matrix with homogeneous entries which satisfies the
twisting equation, as a cochain complex of `R`-modules: the degree-`n` term is
`twistedTotalGrading ℳ ind n` and the differential is the restriction of `twistedDifferential`. -/
noncomputable def twistedCochainComplex : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (twistedTotalGrading ℳ ind) (twistedDifferential m ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      twistedDifferential_mem_twistedTotalGrading m dM hm hM.isHomogeneous hf)
    fun _ f ↦ twistedDifferential_sq_zero m dM hm htw hM f

end SqZero
end TauCeti
end
