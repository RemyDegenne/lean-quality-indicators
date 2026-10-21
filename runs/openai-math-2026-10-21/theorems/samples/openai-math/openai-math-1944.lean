namespace OAI

namespace MetricKMedianRecovery.BitMachine

open Turing Turing.TM2 StateTransition

namespace WordOperations

lemma upd1 (xs ys zs : List Bool) : Function.update (store xs ys) 1 zs=store xs zs := by
  funext i; fin_cases i <;> simp [store]

end WordOperations
end MetricKMedianRecovery.BitMachine
end OAI
