namespace OAI

noncomputable section

open scoped BigOperators Topology

open Set Filter

namespace LeanBlast.CourtadeKumar

theorem monotoneOn_lambdaAuxiliary : MonotoneOn lambdaAuxiliary (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun b hb => (hasDerivAt_lambdaAuxiliary hb.1 hb.2).continuousAt.continuousWithinAt)
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact (hasDerivAt_lambdaAuxiliary hb.1.le hb.2).hasDerivWithinAt
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact lambdaAuxiliaryDerivative_nonneg hb.1 hb.2

end LeanBlast.CourtadeKumar
end
end OAI
