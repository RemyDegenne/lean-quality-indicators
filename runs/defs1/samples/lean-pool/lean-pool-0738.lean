@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

local instance instDecidableEqOfClassical (α : Sort _) : DecidableEq α := Classical.decEq α

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized

variable (V)

variable {V}

scoped notation "^1" => oneAbbrev

variable (T : LOR.TTheory (V := V))

namespace TProof

open Language.Theory.TProof Entailment Entailment.FiniteContext

section «lp_section_1»

variable [R₀Theory T]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def addExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t₁ =' t₂ ==> u₁ =' u₂ ==> (t₁ + u₁) =' (t₂ + u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ==> (t₁ + u₁) =' (t₁ + u₁) ==> (t₁ + u₁) =' (t₂ + u₁) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (#'0 + u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ + u₁) =' (t₂ + u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ==> (t₁ + u₁) =' (t₂ + u₁) ==> (t₁ + u₁) =' (t₂ + u₂) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (t₂.bShift + #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

end «lp_section_1»
end TProof
end Formalized
end Arith
end LO
end «lp_nc_section_1»
end
