namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations.PreKopa.Density

open ProbabilityTheory

theorem densityMomentConstant_pos : 0 < densityMomentConstant := by
  unfold densityMomentConstant
  exact div_pos (mul_pos (by norm_num) (by linarith [pointTailConstant_pos])) (sq_pos_of_pos tailRate_pos)

end SKFluctuations.PreKopa.Density
end
end OAI
