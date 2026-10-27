public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- The first objectwise short complex in the functorial flasque resolution. -/
@[simps]
noncomputable abbrev flasqueEnvelopeShortComplex
    (F : Sheaf AddCommGrpCat X) : ShortComplex (Sheaf AddCommGrpCat X) where
  f := (toFlasqueEnvelope (X := X)).app F
  g := (toFlasqueEnvelopeQuotient (X := X)).app F
  zero := congr_app
    (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) F

end TopCat.Sheaf
end
end
