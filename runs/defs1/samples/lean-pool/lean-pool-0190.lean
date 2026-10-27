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

/-- Imported declaration from the Incompleteness formalization. -/
def dni : 𝓢 ⊢ φ ==> ∼∼φ :=
  deduct' <| negEquiv'.mpr <| deduct <| botOfMemEither (φ := φ) (by simp) (by simp)

end Entailment
end LO
end
