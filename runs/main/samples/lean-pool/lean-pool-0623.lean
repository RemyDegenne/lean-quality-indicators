@[expose] public section

namespace LO

namespace FirstOrder

namespace Rew

open Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

section «lp_section_3»

variable (f : ξ₁ → Semiterm L ξ₂ n)

lemma rewrite_comp_rewrite (v : ξ₂ → Semiterm L ξ₃ n) (w : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) :=
  by ext <;> simp[comp_app]

end «lp_section_3»
end Rew
end FirstOrder
end LO
end
