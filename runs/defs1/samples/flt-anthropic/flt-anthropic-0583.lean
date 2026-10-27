namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolCHint

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Step2

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

abbrev O (k : Fin D.m) : D.X'.Opens := D.ιι ⁻¹ᵁ D.Ω k

end ChartData
end Step2
end SolCHint
end
end P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
