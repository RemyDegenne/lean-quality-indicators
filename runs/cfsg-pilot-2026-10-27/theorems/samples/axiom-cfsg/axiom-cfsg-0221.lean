public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

open scoped commutatorElement Matrix

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem conj_mem (c : Subgroup.centralizer ({z} : Set G)) {q : G} (hq : q ∈ leechQ z) :
    (c : G) * q * (c : G)⁻¹ ∈ leechQ z := by
  have h1 : L.φ ⟨q, L.mem_centralizer hq⟩ = 1 := (L.φ_ker _).2 hq
  have h2 : L.φ (c * ⟨q, L.mem_centralizer hq⟩ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (L.φ_ker _).1 h2

end LeechSystem
end CFSG.Monster.GMS
end
