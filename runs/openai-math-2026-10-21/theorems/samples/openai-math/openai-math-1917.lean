namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

section

section AnalyticAssemblyScope

open scoped BigOperators Topology

section

open Filter Set MeasureTheory

open scoped Topology

open Filter Set Asymptotics

namespace WeightedTorusJets

open _root_.Complex _root_.Erdos970.Complex DirichletCharacter

variable {q : ℕ} [NeZero q]

theorem conductorCompletedL_analyticOrderNatAt_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    analyticOrderNatAt (conductorCompletedL χ) 0 = 0 := by
  rw [analyticOrderNatAt,
    analyticOrderAt_eq_zero.mpr (.inr (conductorCompletedL_ne_zero_at_zero χ hχ hχ1))]
  rfl

end WeightedTorusJets
end
end AnalyticAssemblyScope
end
end Erdos970
end OAI
