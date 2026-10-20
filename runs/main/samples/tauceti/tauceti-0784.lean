public section

namespace TauCeti.ClassGroup

variable (R : Type*) [CommRing R] [IsDomain R]

@[simp] theorem elementaryTwoQuotientMk_one :
    elementaryTwoQuotientMk R (1 : ClassGroup R) = 0 :=
  TauCeti.elementaryTwoQuotientMk_one

end TauCeti.ClassGroup
end
