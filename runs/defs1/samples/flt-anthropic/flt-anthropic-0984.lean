namespace P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace TateRankSol

open Representation

section CharP

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module k V]
  (τ : Representation k G V)

def regRep (d : ℕ) : Representation k G (Fin d → G → k) where
  toFun h :=
    { toFun := fun f i g => f i (h⁻¹ * g)
      map_add' := fun f₁ f₂ => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    refine LinearMap.ext fun f => ?_
    funext i g
    simp
  map_mul' h₁ h₂ := by
    refine LinearMap.ext fun f => ?_
    funext i g
    simp [mul_assoc]

end CharP
end TateRankSol
end
end P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
