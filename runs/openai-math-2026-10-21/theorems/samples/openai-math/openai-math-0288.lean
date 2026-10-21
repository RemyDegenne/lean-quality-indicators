namespace OAI

namespace ContinuumCoulomb.ContactMediator

open MediatorGraph MediatorIteration

theorem spoke_nonneg (r W G : ℕ) (J : ℚ) : 0 ≤ MediatorParameters.spoke r W G J := by
  unfold MediatorParameters.spoke DyadicRootProgram.value
  positivity

end ContinuumCoulomb.ContactMediator
end OAI
