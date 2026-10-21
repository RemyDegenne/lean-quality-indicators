namespace OAI

noncomputable section

namespace ForcedComputation

open ShearFlows

open scoped ContDiff NNReal

theorem phaseSpacePoint_lipschitz : LipschitzWith 1 phaseSpacePoint := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (p - q))).mpr
  intro j
  fin_cases j
  · exact (norm_le_pi_norm (p.2 - q.2) 0).trans (norm_snd_le (p - q))
  · exact (norm_le_pi_norm (p.2 - q.2) 1).trans (norm_snd_le (p - q))
  · exact norm_fst_le (p - q)

end ForcedComputation
end
end OAI
