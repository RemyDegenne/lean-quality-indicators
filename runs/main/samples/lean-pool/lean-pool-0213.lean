@[expose] public section

namespace LO

namespace Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ ψ χ : F}
         {Γ Δ : List F}

open NegationEquiv

open FiniteContext

open List

section «lp_section_1»

omit [DecidableEq F] in
@[simp] lemma «negnegEquiv!» : 𝓢 ⊢! ∼∼φ <=> ((φ ==> ⊥) ==> ⊥) := by
  classical
  exact ⟨negnegEquiv⟩

end «lp_section_1»
end Entailment
end LO
end
