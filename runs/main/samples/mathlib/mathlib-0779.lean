@[expose] public section

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

namespace FiniteMulArchimedeanClass

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

@[to_additive]
theorem mem_closedBallSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ ∀ h : a ≠ 1, c ≤ mk a h := by
  simp

end FiniteMulArchimedeanClass
end
