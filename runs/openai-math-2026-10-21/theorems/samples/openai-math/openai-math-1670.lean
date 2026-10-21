namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped Topology

namespace InvariantIsing

lemma measurable_fieldMajorant (d : ℝ) : Measurable (fieldMajorant d) := by
  unfold fieldMajorant
  fun_prop

end InvariantIsing
end
end OAI
