public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Chevalley

section F429Kinds

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_F429_one_D4two
    (hyp : HypF_4_4 .D4tw 2 1 Gp M₁ M₂) :
    Gp = ⊤ ∨ (Gp.index = 3 ∧ Nat.card E = Nat.card (MulAut ↥Gp)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  exact burnsideF429_eq_top_or_of_card_outer hyp.centralizer_trivial Nat.prime_three
    (burnsideF429_card_outer_D4two hyp.model)

end F429Kinds
end CFSG.ASVolI
end
