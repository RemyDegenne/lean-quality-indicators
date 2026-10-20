public section

namespace TauCeti.ClassGroup

variable (R : Type*) [CommRing R] [IsDomain R]

variable {R}

@[simp] theorem elementaryTwoQuotientCongr_mk {S : Type*} [CommRing S] [IsDomain S]
    (e : ClassGroup R ≃* ClassGroup S) (C : ClassGroup R) :
    elementaryTwoQuotientCongr e (elementaryTwoQuotientMk R C) =
      elementaryTwoQuotientMk S (e C) := by
  -- Reduce the class-group wrapper names to the generic elementary-2 quotient statement.
  change TauCeti.elementaryTwoQuotientCongr e (TauCeti.elementaryTwoQuotientMk C) =
    TauCeti.elementaryTwoQuotientMk (e C)
  exact TauCeti.elementaryTwoQuotientCongr_mk e C

end TauCeti.ClassGroup
end
