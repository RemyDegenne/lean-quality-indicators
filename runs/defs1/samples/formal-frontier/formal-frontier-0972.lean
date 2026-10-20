@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteAddGrp

/-- The standard generator of the additive `finiteCyclic n`. -/
abbrev finiteCyclicGenerator (n : ℕ) [NeZero n] : finiteCyclic n :=
  show ZMod n from 1

end ProfiniteAddGrp
end
