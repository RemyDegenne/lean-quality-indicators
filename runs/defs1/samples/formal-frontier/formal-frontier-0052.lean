public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- The canonical augmentations assemble naturally from sheaves concentrated
in degree zero to their functorial flasque resolutions. -/
@[expose] noncomputable def toFlasqueResolutionNat :
    CochainComplex.single₀ (Sheaf AddCommGrpCat X) ⟶
      (flasqueResolutionNat (X := X)).asFunctor where
  app F := toFlasqueResolution F
  naturality F G f := by
    ext
    change f ≫ (toFlasqueEnvelope (X := X)).app G =
      (toFlasqueEnvelope (X := X)).app F ≫
        (flasqueEnvelopeFunctor (X := X)).map f
    exact (toFlasqueEnvelope (X := X)).naturality f

end TopCat.Sheaf
end
end
