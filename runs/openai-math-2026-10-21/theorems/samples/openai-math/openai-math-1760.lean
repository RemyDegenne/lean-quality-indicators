namespace OAI

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

open CompanionMetropolisWordProgram

attribute [local irreducible] proposalWidth queryWidth

lemma polynomial_values : PolynomialTime valuesRealizer := by
  unfold valuesRealizer
  exact polynomial_composition (polynomial_pair polynomial_proposalWidth
    (polynomial_composition (polynomial_pair polynomial_queryWidth
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_constant [])) polynomial_listCons)) polynomial_listCons)) polynomial_listCons

end ContingencyTables.CompanionTransitionWidth
end OAI
