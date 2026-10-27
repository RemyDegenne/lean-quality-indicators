public section

open Set Filter Topology Metric

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The cutoff at scale `λ`: equal to `1` on the closed ball of radius half the outer radius. -/
@[expose] def recCutoffBump (h ρ lam : ℝ) (hρ1 : ρ < 1) (hlam0 : 0 < lam) : ContDiffBump (0 : ℝ
  × ℝ) where
  rIn := recCutoffRadius h ρ lam / 2
  rOut := recCutoffRadius h ρ lam
  rIn_pos := by have := recCutoffRadius_pos (h := h) hρ1 hlam0; linarith only [this]
  rIn_lt_rOut := by have := recCutoffRadius_pos (h := h) hρ1 hlam0; linarith only [this]

end CIV
end
end
