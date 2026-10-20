public section

open MeasureTheory Set Filter

open scoped ENNReal

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem blowupLimitAssemblyPressure_rieszPressure_congr_ae
    {F G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (h : ∀ i j, F i j =ᵐ[volume] G i j) :
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF =
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) G hG := by
  unfold CKN.Leray.rieszPressureSpaceTime
  congr 1
  unfold CKN.Leray.rieszPressureSpaceTimeTensorToLp
  funext i j
  exact MemLp.toLp_congr (hF i j) (hG i j) (h i j)

end ESS
end
end
