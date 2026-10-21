namespace OAI

noncomputable section

namespace TotientAsymptotic

lemma collisionMesh_le_hundredth {h : ℕ} {δ : ℝ} (hh : 4≤h)
    (hδ : δ≤2/(h : ℝ)^32) : δ≤1/100 := by
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hhR 32
  have h0 : (0 : ℝ)<(h : ℝ)^32 := by positivity
  apply hδ.trans
  apply (div_le_iff₀ h0).mpr
  norm_num at hp
  linarith

end TotientAsymptotic
end
end OAI
