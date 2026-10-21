namespace OAI

noncomputable section

open MeasureTheory Set Filter Real Metric

namespace GeneralMahler

variable {f g:ℝ→ℝ} {n : ℕ}

namespace Layers

lemma lp_test : TestF LP := TestF.of_d d_lp mc_test

end Layers
end GeneralMahler
end
end OAI
