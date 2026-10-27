public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

variable {R' : Type u} [CommRing R'] (φ : R →+* R')

/-- The isomorphism identifying the total space of the base change of `toEllipticCurveGeom W` along
`Spec φ : Spec R' ⟶ Spec R` with the projective model of `W.map φ`. Under it, the structure
morphism of the base change is `(W.map φ).projModelOver`
(`toEllipticCurveGeomBaseChangeIso_hom_projModelOver`), its zero section is
`(W.map φ).projModelZero` (`zero_toEllipticCurveGeomBaseChangeIso_hom`), and its projection to
`toEllipticCurveGeom W` is the base change morphism `W.projModelBaseChange φ`
(`toEllipticCurveGeomBaseChangeIso_hom_projModelBaseChange`). -/
noncomputable def toEllipticCurveGeomBaseChangeIso :
    ((toEllipticCurveGeom W).baseChange (Spec.map (CommRingCat.ofHom φ))).carrier ≅
      (W.map φ).projModel :=
  ((toEllipticCurveGeom W).isPullback_baseChange _).isoIsPullback _ _
    (isPullback_projModelBaseChange_comp_toEllipticCurveGeomIso_inv W φ)

end WeierstrassCurve
end
