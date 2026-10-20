public section

noncomputable section

open ValuativeRel IntermediateField Pointwise

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The unramified quotient** `G_K ⧸ I_K` of the absolute Galois group. -/
abbrev unramifiedQuotient := Field.absoluteGaloisGroup K ⧸ inertiaSubgroup K

end TauCeti
end
end
