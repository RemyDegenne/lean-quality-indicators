@[expose] public section

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

namespace FiniteArchimedeanClass

variable (K)

@[simp]
theorem mem_ball_iff {a : M} {c : FiniteArchimedeanClass M} :
    a ∈ ball K c ↔ ∀ h : a ≠ 0, c < mk a h :=
  mem_ballAddSubgroup_iff

end FiniteArchimedeanClass
end
