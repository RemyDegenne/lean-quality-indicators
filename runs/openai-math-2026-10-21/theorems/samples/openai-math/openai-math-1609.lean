namespace OAI

noncomputable section

namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

@[simp] theorem concreteRademacher_star (n : ℕ) :
    star (concreteRademacher τ hdiff n) = concreteRademacher τ hdiff n :=
  dyadicRademacher_star τ hdiff ⟨1, IsStarProjection.one _⟩ n

end KadisonSimilarity
end
end OAI
