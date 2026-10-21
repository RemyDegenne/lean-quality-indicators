namespace OAI

namespace ContingencyTables.ForestBoxCardinality

open scoped BigOperators Classical

open CompanionFactorialApplication ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

theorem cardinality_le_square (A : Instance I J) (hW : 20*A.d ≤ A.W) :
    Fintype.card (Assignments A) ≤ (∏ a : I×J,(A.b a.1 a.2+1))^2 := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_fin]
  calc
    _ ≤ ∏ a : I×J,(A.b a.1 a.2+1)^2 := by
      apply Finset.prod_le_prod
      intro a _
      exact width_add_one_le_square A hW a.1 a.2
    _ = _ := Finset.prod_pow Finset.univ 2 (fun a : I×J => A.b a.1 a.2+1)

end ContingencyTables.ForestBoxCardinality
end OAI
