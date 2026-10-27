open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- Membership in the image of the paper's principal RV classes inside the degree-graded
graded ring. -/
def IsPrincipalRVImage (x : DegreeGraded K) : Prop :=
  ∃ B : HahnDegreeRV K, IsPrincipalRV B ∧
    (degreeValuation K).rvInitialFormHom B = x

end
end Berarducci
