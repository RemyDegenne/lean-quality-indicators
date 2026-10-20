@[expose] public section

open Function Multiplicative

open Finset hiding card

open Fintype (card)

namespace AddChar

section CommSemiring

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

variable [CharZero R]

lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := sum_eq_zero_iff_ne_zero.not_left

end CommSemiring
end AddChar
end
