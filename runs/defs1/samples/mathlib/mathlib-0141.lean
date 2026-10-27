@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

section

open AlgebraicGeometry.ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `openToLocalization` maps. -/
def stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ⟶ ↧(at x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

end
end AlgebraicGeometry
end
end
