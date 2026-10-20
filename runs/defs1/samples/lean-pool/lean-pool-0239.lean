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
def demorgan₂ : 𝓢 ⊢ (∼φ ⋏ ∼ψ) ==> ∼(φ ⋎ ψ) := by
  apply andImplyIffImplyImply'.mpr;
  apply deduct';
  apply deduct;
  apply negEquiv'.mpr;
  apply deduct;
  exact or₃''' (negEquiv'.mp FiniteContext.byAxm) (negEquiv'.mp FiniteContext.byAxm)
    (FiniteContext.byAxm (φ :=
    φ ⋎ ψ));

end Entailment
end LO
end
