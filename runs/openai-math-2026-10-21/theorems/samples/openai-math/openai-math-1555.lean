namespace OAI

namespace ContingencyTables.ProfilePrograms

open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_marginValue (row : Bool) : PolynomialTime (marginValueRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_marginList row)) polynomial_second)
    (polynomial_getDFast 0)

end ContingencyTables.ProfilePrograms
end OAI
