namespace P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField

set_option autoImplicit false

universe u v w

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicGeometry

p2m_open

open CategoryTheory Opposite

p2m_reactivate

namespace AlgebraicGeometry

namespace RelPicard

namespace LFP

p2m_open

section VertexGeo

p2m_open

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (Γ : Type u) [CommRing Γ] [Algebra R Γ]

noncomputable def vtxHom (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) (D : FGSubalgebra R A) :
    letI := algebraOfPresent R A Γ U eU; tensorStage R A Γ D →ₐ[Γ] U :=
  letI := algebraOfPresent R A Γ U eU
  (vtxEquiv R A Γ U eU : Γ ⊗[R] A →ₐ[Γ] U).comp (tensorStageToColimit R A Γ D)

end VertexGeo
end LFP
end RelPicard
end AlgebraicGeometry
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
