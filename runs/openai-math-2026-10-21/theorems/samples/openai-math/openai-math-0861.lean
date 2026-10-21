namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

section ClusterLocality

attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_mono_local (G : BondGraph V E) (x : V) : Monotone (reachBall G x) :=
  monotone_nat_of_le_succ (reachBall_le_step G x)

end ClusterLocality
end Percolation
end OAI
