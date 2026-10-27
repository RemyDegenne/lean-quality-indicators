@[expose] public section

namespace LO

namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

variable {𝓢 : S}

namespace KTc

variable [Entailment.KTc 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFive : 𝓢 ⊢ ◇φ ==> □◇φ := axiomTc

end KTc
end Entailment
end LO
end
