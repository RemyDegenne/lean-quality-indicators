public section

open MulAction

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]

@[simp]
theorem quotientStabilizerEquiv_mk (b : X) (g : G) :
    quotientStabilizerEquiv G b (QuotientGroup.mk g) = g • b :=
  ofQuotientStabilizer_mk G b g

end TauCeti
end
