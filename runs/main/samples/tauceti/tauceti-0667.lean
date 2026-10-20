public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory MulOpposite

open scoped TensorProduct

universe v uk uA uB

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]

variable (Γ : InternalGrading k A) [GradedAlgebra Γ.piece]

@[simp]
theorem bimoduleUnitEquiv_symm_smul (a : A) (b : Aᵐᵒᵖ) (x : bimoduleUnit.{v} Γ) :
    (bimoduleUnitEquiv.{v} Γ).symm ((a ⊗ₜ[k] b) • x) =
      a * (bimoduleUnitEquiv.{v} Γ).symm x * unop b :=
  unitEquiv_symm_smul a b x

end TauCeti.GradedModuleCat
end
end
