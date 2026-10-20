public section

namespace TauCeti.Huber

open Filter

open scoped Topology

variable {n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NonarchimedeanRing R]

section Complete

variable [CompleteSpace R]

/-- Over a complete coefficient ring, the completed Gauss comparison is an algebra equivalence.
It composes the completion's coefficient-algebra comparison with the identity on series. -/
noncomputable def restrictedMvPowerSeriesCompletionGaussAlgEquiv :
    restrictedMvPowerSeriesCompletion n R ≃ₐ[R]
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesCompletionAlgEquiv n R).trans restrictedMvPowerSeriesGaussAlgEquiv

end Complete
end TauCeti.Huber
end
