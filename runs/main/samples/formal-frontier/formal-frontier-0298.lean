public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

@[simp]
theorem flasqueEnvelopeQuotientIterate_succ (n : ℕ) :
    flasqueEnvelopeQuotientIterate (X := X) (n + 1) =
      flasqueEnvelopeQuotientIterate (X := X) n ⋙
        flasqueEnvelopeQuotientFunctor (X := X) := rfl

end TopCat.Sheaf
end
end
