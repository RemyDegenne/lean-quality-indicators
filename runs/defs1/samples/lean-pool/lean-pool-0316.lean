@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

noncomputable local instance matrixComplexContinuousENormPartThree
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open WithLp

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The finite equivalence encoding DSV density rational public log phase target first index. -/
def dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    (B N d L m : ℕ) :
    (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
      B N d L × Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicLogPhaseResidual B N d L m) :=
  (Equiv.prodCongr
    (dSVDensityRationalPublicLogPhaseTargetSplitEquiv B N d L)
    (Equiv.refl (Fin m))).trans
      (dSVRankControlledTargetCatalystIndexEquiv
        (ι := DSVDensityRationalPublicLogPhaseCatalystIndex
          B N d L) d m)

end
end QuantumParallelRepetition
end
end
