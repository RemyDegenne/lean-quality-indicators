@[expose] public section

namespace LO

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]

variable {𝓢 : S} {φ ψ χ : F}

infixl:90 "⨀" => mdp

infixl:90 "⨀" => mdp!

section «lp_section_1»

variable [ModusPonens 𝓢]

infixl:90 "⨀₁" => mdp₁

infixl:90 "⨀₁" => mdp₁!

infixl:90 "⨀₂" => mdp₂

infixl:90 "⨀₂" => mdp₂!

infixl:90 "⨀₃" => mdp₃

infixl:90 "⨀₃" => mdp₃!

infixl:90 "⨀₄" => mdp₄

infixl:90 "⨀₄" => mdp₄!

@[simp] lemma «implyLeftVerum!» [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! φ ==> ⊤ :=
  ⟨implyLeftVerum⟩

end «lp_section_1»
end Entailment
end LO
end
