public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem mem_torusSL_iff_exists {p : ℕ} {z : SL(3, K)} :
    z ∈ torusSL K p ↔ ∃ y : Kˣ × Kˣ, y.1 ^ p = 1 ∧ y.2 ^ p = 1 ∧ diagHom y = z := by
  rw [torusSL, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_prod, mem_rootsOfUnity, mem_rootsOfUnity] at hy
    exact ⟨y, hy.1, hy.2, rfl⟩
  · rintro ⟨y, h1, h2, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_prod, mem_rootsOfUnity, mem_rootsOfUnity]
    exact ⟨h1, h2⟩

end Torus
end CFSG.Quasithin.H13.NQCore.L3Odd
end
