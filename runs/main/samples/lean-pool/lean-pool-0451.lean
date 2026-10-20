@[expose] public section

namespace LO

namespace FirstOrder

namespace Rew

open Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

section «lp_section_14»

lemma fixitr_succ (m) :
    fixitr (L := L) n (m + 1) = Rew.fix.comp (fixitr n m) := by
  simp [fixitr]

end «lp_section_14»
end Rew
end FirstOrder
end LO
end
