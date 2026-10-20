@[expose] public section

namespace LO

namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

variable {𝓢 : S} [Entailment.K 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ ==> □^[n](φ ⋏ ψ) := by
  have d₁ : 𝓢 ⊢ □^[n]φ ==> □^[n](ψ ==> φ ⋏ ψ) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](ψ ==> φ ⋏ ψ) ==> (□^[n]ψ ==> □^[n](φ ⋏ ψ)) := multiboxAxiomK;
  exact (and₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans'' d₁ d₂);

end Entailment
end LO
end
