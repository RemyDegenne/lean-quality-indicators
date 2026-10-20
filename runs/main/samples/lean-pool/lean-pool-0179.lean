@[expose] public section

namespace LO

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]

variable {𝓢 : S}

section «lp_section_18»

variable [HasAxiomTc 𝓢]

@[simp] lemma «axiomTc!» : 𝓢 ⊢! φ ==> □φ := ⟨axiomTc⟩

end «lp_section_18»
end Entailment
end LO
end
