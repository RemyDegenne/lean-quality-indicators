namespace P2MW.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub

universe u v w w'

open PDivisibleGroup.Hopf

namespace PDivisibleGroup

namespace CRSE95

p2m_open

section Idempotents

variable {A : Type*} [CommRing A]

theorem eq_zero_or_eq_one_of_isIdempotentElem [IsLocalRing A] {e : A}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).1 he)
  · left
    have h1 : (1 - e) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit h).1 he.one_sub
    have := congrArg (fun x => 1 - x) h1
    simpa using this

end Idempotents
end CRSE95
end PDivisibleGroup
end P2MW.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
