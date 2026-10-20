namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

local infixr:73 " ⨳ " => HSMul.hSMul

namespace P2mFamFG

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf HomogeneousLocalization ProjSpaceCech

section Algebra

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}

variable {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ}

variable (ι) in

def uprod (j : Fin (r + 1)) (a : Fin (r + 1) → ℕ) : Γ(P, pullbackChart ι j) := ∏ l, frameUnit ι j l ^ a l

end Algebra
end P2mFamFG
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule_of_isFinite
