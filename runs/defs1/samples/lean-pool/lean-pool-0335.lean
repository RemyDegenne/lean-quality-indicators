@[expose] public section

namespace LongGapsBetweenPrimes

noncomputable section

/-- Coordinates assigned to a nonconstant local basis function. -/
def assignmentSupport {α : Type*} [Fintype α] {k : ℕ}
    (σ : α → Option (Fin k)) : Finset α := Finset.univ.filter fun p => (σ p).isSome

end
end LongGapsBetweenPrimes
end
