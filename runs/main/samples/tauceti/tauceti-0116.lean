public section

namespace TauCeti

variable (p : ℕ) (A : Type*) [Semiring A] (M : Type*) [AddCommMonoid M] [Module A M]

variable {p A M}

@[simp]
theorem mem_pPowerTorsion_iff {x : M} : x ∈ pPowerTorsion p A M ↔ ∃ k : ℕ, p ^ k • x = 0 :=
  .rfl

end TauCeti
end
