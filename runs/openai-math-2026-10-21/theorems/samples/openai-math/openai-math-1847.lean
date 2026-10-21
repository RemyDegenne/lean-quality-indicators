namespace OAI

namespace Superstring.PrefixGreedy

open BitCode

variable {α : Type} [Coded α]

variable [DecidableEq α]

@[fun_prop] theorem poly_step : Poly (step : State α → State α) := by
  unfold step
  fun_prop

end Superstring.PrefixGreedy
end OAI
