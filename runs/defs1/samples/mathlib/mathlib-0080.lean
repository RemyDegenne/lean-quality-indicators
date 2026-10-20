@[expose] public section

variable {α : Type*}

namespace FirstOrder

namespace Ring

open ringFunc Language

/-- `RingFunc.one`, but with the defeq type `Language.ring.Functions 0` instead
of `RingFunc 0` -/
abbrev oneFunc : Language.ring.Functions 0 := one

end Ring
end FirstOrder
end
