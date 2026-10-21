namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

lemma oneDim_inner (v : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v=v 0 := by
  simp [PiLp.inner_apply]

end SphericalPerceptronFreeEnergy
end
end OAI
