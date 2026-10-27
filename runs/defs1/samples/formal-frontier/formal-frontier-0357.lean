public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- Iterates of the quotient functor used in the functorial flasque resolution. -/
@[expose] noncomputable def flasqueEnvelopeQuotientIterate :
    ℕ → (Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X)
  | 0 => Functor.id _
  | n + 1 => flasqueEnvelopeQuotientIterate n ⋙
      flasqueEnvelopeQuotientFunctor (X := X)

end TopCat.Sheaf
end
end
