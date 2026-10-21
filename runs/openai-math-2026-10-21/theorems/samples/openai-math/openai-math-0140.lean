namespace OAI

namespace MetricKMedianRecovery

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma inactive_frozen (j : D) (hj : ¬activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s'.budget j = s.budget j := by
  cases H <;> simp only [regularUpdate, freeUpdate, phaseUpdate, hj, ↓reduceIte]

end AtomicStep
end MetricKMedianRecovery
end OAI
