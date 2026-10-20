@[expose] public section

noncomputable section

namespace PeriodPair

variable (a : ℂˣ) (L : PeriodPair)

@[simp] lemma smulLatticeEquiv_coe (l : L.lattice) :
    ((smulLatticeEquiv a L l : (a • L).lattice) : ℂ) = (a : ℂ) * (l : ℂ) := rfl

end PeriodPair
end
end
