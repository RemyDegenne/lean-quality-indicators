namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField

set_option autoImplicit false

universe u

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TrivSqZeroExt

noncomputable section

set_option quotPrecheck false

namespace P2mTJ2

section Charts

variable {K : Type u} [CommRing K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of K))

variable (A : Type u) [CommRing A] [Algebra K A]

def E01 : (A ⊗[K] (𝒱.cover c).A01) ≃ₐ[A]
    ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A))).A01 :=
  (exists_chartIsos 𝒱 c A).choose_spec.choose_spec.choose

end Charts
end P2mTJ2
end
end P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
