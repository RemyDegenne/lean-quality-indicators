@[expose] public section

universe u

noncomputable section

variable (K : Type u) [Field K]

namespace ValuationSubring

variable {K}

variable (A : ValuationSubring K)

section nonunits

variable {A}

theorem nonunits_le : A.nonunits ≤ A.toNonUnitalSubring := fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le

end nonunits
end ValuationSubring
end
end
