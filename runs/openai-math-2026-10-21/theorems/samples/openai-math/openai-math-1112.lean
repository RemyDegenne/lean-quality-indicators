namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators ContDiff Topology

open Set Filter

open scoped Topology BigOperators

namespace ShearFlows

namespace QBall

theorem contains_exact (q : ℚ) : (exact q).Contains q := by simp [Contains, exact]

end QBall
end ShearFlows
end
end OAI
