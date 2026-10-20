@[expose] public section

namespace LO

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]

variable {𝓢 : S}

section «lp_section_15»

variable [HasAxiomDot2 𝓢]

@[simp] lemma «axiomDot2!» : 𝓢 ⊢! ◇□φ ==> □◇φ := ⟨axiomDot2⟩

end «lp_section_15»
end Entailment
end LO
end
