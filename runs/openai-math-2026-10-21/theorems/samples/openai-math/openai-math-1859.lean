namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCompleteCommon

open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport

open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve

local notation "O" => ActualEisensteinCubic.O

theorem residualPart_one_right (I : Ideal O) (hI : I ≠ 0) : residualPart I 1 = I := by
  apply residualPart_eq_of_empty I 1 hI
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

end SevenEighths.CenteredMomentCompleteCommon
end
end OAI
