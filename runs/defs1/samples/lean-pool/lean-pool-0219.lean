@[expose] public section

namespace LO

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]

variable {𝓢 : S}

section «lp_section_19»

variable [HasAxiomDiaT 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def diaT : 𝓢 ⊢ ◇φ ==> φ := HasAxiomDiaT.diaT _

end «lp_section_19»
end Entailment
end LO
end
