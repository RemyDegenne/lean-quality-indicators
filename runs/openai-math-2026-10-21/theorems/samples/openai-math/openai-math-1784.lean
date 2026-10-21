namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets.W11

open SiegelZeros.W10

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

theorem squarefreeTau_a (ar br : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : ar ^ 2 = (d : K)) (hb : br ^ 2 = 2) :
    squarefreeFieldSignAction ar br d hd hd1 hd2 ha hb false true
      (adjoinGenerators ar br 1) = adjoinGenerators ar br 1 := by simp

end WeightedTorusJets.W11
end SiegelZeros
end OAI
