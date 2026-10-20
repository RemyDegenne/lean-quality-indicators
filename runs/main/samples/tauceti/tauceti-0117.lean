public section

namespace TauCeti

section Prod

variable (G H : Type*) [CommGroup G] [CommGroup H]

@[simp] theorem elementaryTwoQuotientProdLinearEquiv_mk (G H : Type*) [CommGroup G] [CommGroup H]
    (p : G × H) :
    elementaryTwoQuotientProdLinearEquiv G H (elementaryTwoQuotientMk p) =
      (elementaryTwoQuotientMk p.1, elementaryTwoQuotientMk p.2) :=
  elementaryTwoQuotientProdAddEquiv_mk G H p

end Prod
end TauCeti
end
