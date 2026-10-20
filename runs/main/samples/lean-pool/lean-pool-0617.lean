@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

local instance instDecidableEqOfClassical₂ (α : Sort _) : DecidableEq α := Classical.decEq α

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

variable [DefinableLanguage L]

variable {T : Theory L} [T.Delta1Definable]

open Derivation2

section «lp_section_2»

variable {T : Theory ℒₒᵣ} [T.Delta1Definable]

theorem provableₐ_of_provable {σ} : T ⊢! σ → T.Provableₐ (⌜σ⌝ : V) := fun h ↦
  Language.Theory.Derivable.of_ss Formalized.theory_subset_AddR₀ (provable_of_provable h)

end «lp_section_2»
end Arith
end LO
end «lp_nc_section_1»
end
