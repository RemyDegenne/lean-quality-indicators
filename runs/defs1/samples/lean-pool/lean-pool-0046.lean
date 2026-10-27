@[expose] public section

namespace LO

namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

variable {𝓢 : S} [Entailment.K 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxDistribute' (h : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ □φ ==> □ψ := implyMultiboxDistribute' (n := 1) h

end Entailment
end LO
end
