namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolCHint

section Setup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

attribute [scoped instance] ChartData.hc

namespace ChartData

variable {f} (D : ChartData f)

scoped instance (k : Fin D.m) : IsImmersion (D.ι k) := by unfold ι; infer_instance

abbrev prπ : D.PiS ⟶ Spec (CommRingCat.of A) := ProjSpace.prodOverπ A D.e

end ChartData
end Setup
end SolCHint
end
end P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
