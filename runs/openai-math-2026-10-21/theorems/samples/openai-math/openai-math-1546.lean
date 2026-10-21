namespace OAI

section

namespace Erdos3.FixedDensity

namespace AdaptiveCoarseTargetSchedule

namespace Landing

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

end Landing
end AdaptiveCoarseTargetSchedule
end Erdos3.FixedDensity
end
end OAI
