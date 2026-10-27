public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

omit [Finite G] in
theorem eq_one_of_mem_zpowers_of_eq_inv {a x : G} (ha3 : a ^ 3 = 1) (hx : x ∈ zpowers a)
    (h : x = x⁻¹) : x = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : (a ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [ha3]
  have h2 : a ^ j * a ^ j = 1 := mul_eq_one_iff_eq_inv.mpr h
  calc a ^ j = (a ^ j * a ^ j) * a ^ j := by rw [h2, one_mul]
    _ = (a ^ j) ^ 3 := (pow_three' _).symm
    _ = 1 := h3

end Setup
end CFSG.Sporadic.Recognition.JankoWong
end
