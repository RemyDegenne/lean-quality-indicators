namespace OAI

namespace Erdos970

section

open Set MeasureTheory

namespace Erdos970Dependency.DeficitIntegralValues

open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals

theorem shift_indicator (f : ℝ → ℝ) (a d : ℝ) :
    (fun s ↦ (Ioi a).indicator f (s - d)) = (Ioi (a + d)).indicator (fun s ↦ f (s - d)) := by
  funext s
  by_cases hs : a + d < s
  · rw [indicator_of_mem (show s ∈ Ioi (a + d) from hs),
      indicator_of_mem (show s - d ∈ Ioi a by change a < s - d; linarith)]
  · rw [indicator_of_notMem (show s ∉ Ioi (a + d) from hs),
      indicator_of_notMem (show s - d ∉ Ioi a by change ¬a < s - d; linarith)]

end Erdos970Dependency.DeficitIntegralValues
end
end Erdos970
end OAI
