namespace OAI

namespace ContinuumCoulomb.MediatorIteration

open Matrix MediatorGraph

open scoped BigOperators Kronecker InnerProductSpace

theorem central_noLoops (n r : ℕ) (Delta : ℚ) : (central n r Delta).NoLoops := by
  intro e h
  have hpair := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
  have := congrArg Prod.snd hpair
  norm_num at this

end ContinuumCoulomb.MediatorIteration
end OAI
