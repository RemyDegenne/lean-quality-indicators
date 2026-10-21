namespace OAI

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

open CompanionMultiplierMatrixProgram

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

lemma polynomial_weight : PolynomialTime weightRealizer :=
  polynomial_composition polynomial_weightInput RootedLabelWeightProgram.polynomial_output

end ContingencyTables.CompanionEvaluatedWeightProgram
end OAI
