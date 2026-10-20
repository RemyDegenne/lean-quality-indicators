@[expose] public section

noncomputable section

section

open Module MeasureTheory Set

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- A coordinate fourier gaussian used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussian L b a x

end NumberField.Odlyzko
end
end
end
