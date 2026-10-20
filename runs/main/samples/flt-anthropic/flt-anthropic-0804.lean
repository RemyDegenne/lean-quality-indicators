namespace P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u

p2m_open

open scoped TensorProduct

p2m_reactivate

namespace PicTanF

section Main

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

theorem ρ0_split (a b : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0
        (ι0 c A 𝒱 a + algebraMap (DualNumber A) _ DualNumber.eps * ι0 c A 𝒱 b) =
      ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) +
        algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 b) := by
  rw [map_add, map_mul, AlgHom.commutes, ← map0_eq, ← map0_eq, ← HomOver.map01_ρ0, ← HomOver.map01_ρ0]
  rfl

end Main
end PicTanF
end P2MW.S_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
