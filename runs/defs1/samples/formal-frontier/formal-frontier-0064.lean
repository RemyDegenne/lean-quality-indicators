@[expose] public section

noncomputable section

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

/-- Projection of all free entries onto the surviving variables. -/
def killForbidden :
    MvPolynomial (UnitriangularCoordinateRing.StrictUpperPair (Fin n)) K →ₐ[K]
      MvPolynomial (SurvivingPair n r) K :=
  MvPolynomial.killCompl (survivingInclusion_injective n r)

end UnitriangularStageCoordinateRing
end
end
