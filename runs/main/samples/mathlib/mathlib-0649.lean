public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation3 "e(" P "|" R ")" =>
  Ideal.ramificationIdx P R

open IsLocalRing Algebra

section IsUnramifiedIn

namespace Algebra

theorem isUnramifiedIn_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedIn S (⊥ : Ideal R) := by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

end Algebra
end IsUnramifiedIn
end
