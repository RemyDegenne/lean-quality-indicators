@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open WithLp

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/--
The DSV density rational heterogeneous target first spectral alice construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ :=
  dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ))

end
end QuantumParallelRepetition
end
end
