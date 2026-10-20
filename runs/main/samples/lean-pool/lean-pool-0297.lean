@[expose] public section

namespace ChainOfLoops

open Utilities Bananas

namespace Loop

@[simp] theorem factor_period (P : Loop) : P.factor.period = P.torsionOrder := rfl

end Loop
end ChainOfLoops
end
