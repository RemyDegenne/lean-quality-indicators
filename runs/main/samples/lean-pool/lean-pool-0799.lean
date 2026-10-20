public section

open MeasureTheory Set Filter

open CKN.Foundation.Heat CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem heatRegEnergy_fderiv_eq_sum {η : ℝ} (hη : 0 < η) (v w : Vec3) :
    fderiv ℝ (heatRegEnergy η) v w = ∑ i : Fin 3, heatRegTest η v i * w i := by
  rw [heatRegEnergy_fderiv hη, heatRegTest_pairing]

end ESS
end
end
