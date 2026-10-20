public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

attribute [instance] AbelianVariety.grpObj AbelianVariety.isProper
  AbelianVariety.geometricallyIntegral

/-- The residue field of an abelian variety at its identity is canonically the ground field `K`,
through the evaluation map of the zero section. -/
noncomputable def zeroResidueFieldRingEquiv (A : AbelianVariety K) :
    IsLocalRing.ResidueField (A.toScheme.presheaf.stalk A.zeroPoint) ≃+* K :=
  residueFieldRingEquivOfSection (zeroSection_comp_toOver_hom A)

end AbelianVariety
end AlgebraicGeometry
end TauCeti
end
