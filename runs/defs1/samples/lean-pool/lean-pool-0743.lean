@[expose] public section

noncomputable section

namespace NavierStokes.ActivationStocks

open Set Filter ProfileHistories StressActivation

open scoped Topology ContDiff

open ActivationBounds (ScaledPoint scaledDomain scaledDistance)

/-- Parameter differentiation preserves the same flat-distance factor. -/
noncomputable def etaPair {J : Set ℝ} (hJ : IsOpen J) (A : StockPair J) : StockPair J where
  actual := ActivationBounds.etaD A.actual
  reference := ActivationBounds.etaD A.reference
  factor := ActivationBounds.etaD A.factor
  actual_smooth := ActivationBounds.etaD_smooth hJ A.actual_smooth
  reference_smooth := ActivationBounds.etaD_smooth hJ A.reference_smooth
  factor_smooth := ActivationBounds.etaD_smooth hJ A.factor_smooth
  difference := by
    intro q hq
    have he := ActivationBounds.etaD_congr hJ A.difference hq
    have hs : ActivationBounds.etaD (fun z => A.actual z - A.reference z) q =
        ActivationBounds.etaD A.actual q - ActivationBounds.etaD A.reference q :=
      ((ActivationBounds.etaD_hasDerivAt hJ A.actual_smooth hq).sub
        (ActivationBounds.etaD_hasDerivAt hJ A.reference_smooth hq)).deriv
    rw [hs, ActivationBounds.etaD_scaledDistance_mul] at he
    exact he

end NavierStokes.ActivationStocks
end
end
