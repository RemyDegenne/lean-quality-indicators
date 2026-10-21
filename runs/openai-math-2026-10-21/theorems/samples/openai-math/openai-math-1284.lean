namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCompleteCommon

open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport

open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve

local notation "O" => ActualEisensteinCubic.O

theorem commonPart_eq_supportExtract (I J : Ideal O) :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

end SevenEighths.CenteredMomentCompleteCommon
end
end OAI
