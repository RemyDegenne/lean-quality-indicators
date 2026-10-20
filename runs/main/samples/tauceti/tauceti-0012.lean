public section

noncomputable section

open scoped WithZero

open IsDedekindDomain Polynomial

namespace TauCeti

namespace Place

variable (k : Type*) [Field k]

variable {k}

variable (k)

variable {k}

variable (k)

variable {k}

variable (k)

variable {k}

variable (k)

@[simp]
theorem ratFuncDegreeOneEquiv_some (a : k) :
    (ratFuncDegreeOneEquiv k (some a) : Place k (RatFunc k)) =
      adicOfIrreducible (irreducible_X_sub_C a) :=
  (rfl)

end Place
end TauCeti
end
end
