namespace OAI

open scoped ENNReal

noncomputable section

open Filter

open scoped Topology

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

namespace TraceReconstruction

open scoped Classical

theorem source_warmup_score_margin (B D : ℕ) {d : ℝ} (hB : 2≤ B)
    (hd : 11/5≤ d) (hd' : d≤3+(B:ℝ)*D) :
    27/50≤ scaleA 2 0 (sourceEpsilon B D)*d ∧ scaleA 2 1 (sourceEpsilon B D)≤1/2 := by
  have he := sourceEpsilon_pos B D
  have hloss := sourceEpsilon_loss B D 2 d hB (by linarith only [hd]) hd'
  norm_num only [show (2:ℝ)^2=4 by norm_num,Nat.cast_ofNat] at hloss
  have hlo := mul_le_mul_of_nonneg_right (scaleA_zero_simple_lower 2 (sourceEpsilon B D) he.le)
    (show 0≤ d by linarith only [hd])
  norm_num only [show (2:ℝ)^2=4 by norm_num] at hlo
  constructor
  · nlinarith only [hloss,hlo,hd,he]
  · have hh := scaleA_le_geometric 2 1 (sourceEpsilon B D) he.le (by omega)
    norm_num at hh ⊢
    exact hh

end TraceReconstruction
end
end
end
end
end
end
end OAI
