public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- The degree-`n` differential in the functorial flasque resolution. -/
@[expose] noncomputable def flasqueResolutionDifferential (n : ℕ) :
    flasqueResolutionFunctor (X := X) n ⟶
      flasqueResolutionFunctor (X := X) (n + 1) where
  app F :=
    (toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
      (toFlasqueEnvelope (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) (n + 1)).obj F)
  naturality {F G} f := by
    change
      (flasqueEnvelopeFunctor (X := X)).map
          ((flasqueEnvelopeQuotientIterate (X := X) n).map f) ≫
        ((toFlasqueEnvelopeQuotient (X := X)).app
            ((flasqueEnvelopeQuotientIterate (X := X) n).obj G) ≫
          (toFlasqueEnvelope (X := X)).app
            ((flasqueEnvelopeQuotientFunctor (X := X)).obj
              ((flasqueEnvelopeQuotientIterate (X := X) n).obj G))) =
      ((toFlasqueEnvelopeQuotient (X := X)).app
          ((flasqueEnvelopeQuotientIterate (X := X) n).obj F) ≫
        (toFlasqueEnvelope (X := X)).app
          ((flasqueEnvelopeQuotientFunctor (X := X)).obj
            ((flasqueEnvelopeQuotientIterate (X := X) n).obj F))) ≫
        (flasqueEnvelopeFunctor (X := X)).map
          ((flasqueEnvelopeQuotientFunctor (X := X)).map
            ((flasqueEnvelopeQuotientIterate (X := X) n).map f))
    rw [← Category.assoc,
      (toFlasqueEnvelopeQuotient (X := X)).naturality
        ((flasqueEnvelopeQuotientIterate (X := X) n).map f),
      Category.assoc]
    have hη := (toFlasqueEnvelope (X := X)).naturality
      ((flasqueEnvelopeQuotientFunctor (X := X)).map
        ((flasqueEnvelopeQuotientIterate (X := X) n).map f))
    simp only [Functor.id_map] at hη
    rw [hη, ← Category.assoc]

end TopCat.Sheaf
end
end
