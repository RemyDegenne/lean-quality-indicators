public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative TensorProduct

namespace TauCeti.Toric

section Scheme

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- The affine toric scheme of a product cone is canonically the fibre product of the
factor affine toric schemes over `Spec ℂ`. -/
noncomputable def affineToricSchemeProdIso :
    affineToricScheme (hi.prod hi') (σ.prod τ) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi' τ)))) :=
  Scheme.Spec.mapIso
    (affineCoordinateRingProdEquiv hi hi' σ τ).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso ℂ (affineCoordinateRing hi σ) (affineCoordinateRing hi' τ)).symm

end Scheme
end TauCeti.Toric
end
