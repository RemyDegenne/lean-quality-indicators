namespace OAI

noncomputable section

namespace ScalarConductivity

open Real Set Filter Topology MeasureTheory

lemma connectorProfile_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorProfile K z = connectorProfile K (K+2)*exp (-3*(z-(K+2))) := by
  have hi : (∫ t in (K+2)..z, connectorRate K t) = 3*(z-(K+2)) := by
    calc
      _ = ∫ _t in (K+2)..z, (3:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        apply connectorRate_right hK
        exact le_trans (le_min (by linarith) hz) ht.1)
      _ = _ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((connectorRate_smooth K).continuous.intervalIntegrable 0 (K+2))
    ((connectorRate_smooth K).continuous.intervalIntegrable (K+2) z)
  rw [hi] at hadd
  unfold connectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
  ring

end ScalarConductivity
end
end OAI
