@[expose] public section

set_option warningAsError true

noncomputable section

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι] [LinearOrder ι]

theorem upperTriangularGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (upperTriangularGroupUnderlyingScheme K ι).left =
      ((Fintype.card ι + (Fintype.card ι).choose 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim
    (PrimeSpectrum (UpperTriangularCoordinateRing.CoordinateRing K ι)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact upperTriangularCoordinateRing_ringKrullDim K ι

end AlgebraicGeometry
end
end
