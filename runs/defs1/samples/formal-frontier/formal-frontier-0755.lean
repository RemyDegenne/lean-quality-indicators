public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- The natural projection onto the functorial quotient. -/
noncomputable abbrev toFlasqueEnvelopeQuotient :
    flasqueEnvelopeFunctor (X := X) ⟶
      flasqueEnvelopeQuotientFunctor (X := X) :=
  cokernel.π (toFlasqueEnvelope (X := X))

end TopCat.Sheaf
end
end
