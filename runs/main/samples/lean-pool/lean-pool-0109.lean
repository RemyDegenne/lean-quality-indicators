public noncomputable section

open Set MvPolynomial

open scoped NatOrdinal DirectSum

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

theorem represents_zero (m : NatOrdinal.{u}) :
    Represents (0 : Nonpositive G K) m 0 :=
  (ν).represents_zero m

end HahnSeries.Nonpositive
end
