@[expose] public section

open scoped InnerProductSpace ENNReal CompactlySupported

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {a : H →L[ℂ] H}

section Pair

variable (ha : IsStarNormal a)

/-- The **polarised diagonal integral** of a symbol at a pair of vectors.  For
continuous symbols this is `⟪ψ, cfcHom f ξ⟫`; it is the blueprint for the
matrix elements of the bounded Borel calculus. -/
noncomputable def pair (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ((∫ x, f x ∂(diagMeasure ha (ξ + ψ)))
      + Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ + Complex.I • ψ)))
      - (∫ x, f x ∂(diagMeasure ha (ξ - ψ)))
      - Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ - Complex.I • ψ))))

end Pair
end BorelCalculus
end TauCeti
end
