@[expose] public section

universe u v w

open CategoryTheory

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type u) [CommRing R]

@[simp]
theorem tensorMul_of_module
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    tensorMul R (of R M) (of R N) = of R (M ⊗[Rᵐᵒᵖ] N) := by
  rw [← of_repr R M, ← of_repr R N, tensorMul_of]
  exact of_eq_of_equiv R _
    (TensorProduct.congr (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
      (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ N))

end KTheory.ProjectiveClass
end
