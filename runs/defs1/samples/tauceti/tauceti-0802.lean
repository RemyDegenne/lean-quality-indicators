public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial IsLocalRing

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

variable [IsLocalRing R]

/-- Over a local ring `R`, the sections of the structure morphism `projModel W ⟶ Spec R` of the
projective Weierstrass model correspond to the projective point classes `[X : Y : Z]` of solutions
of the projective Weierstrass equation with unimodular coordinates, that is, with one coordinate a
unit. The class of a representative `P` with unit coordinate `Pᵢ` corresponds to the section
through the chart `D₊(Xᵢ)` at which `Xₖ / Xᵢ = Pₖ / Pᵢ` (`projModelPointsEquivUnimodular_symm_mk`).
The zero section `[0 : 1 : 0]` corresponds to the class of `(0, 1, 0)`
(`projModelPointsEquivUnimodular_projModelZero`), and the section through the chart `D₊(Z)` at which
`X / Z = x` and `Y / Z = y` to the class of `(x, y, 1)`
(`projModelPointsEquivUnimodular_symm_mk_some`). No ellipticity is assumed. -/
noncomputable def projModelPointsEquivUnimodular :
    {g : Spec (CommRingCat.of R) ⟶ projModel W //
      g ≫ projModelOver W = 𝟙 (Spec (CommRingCat.of R))} ≃
      {P : Projective.PointClass R // W.toProjective.UnimodularLift P} :=
  (Equiv.ofBijective _ W.sectionOfClass_bijective).symm

end CommRing
end WeierstrassCurve
end
