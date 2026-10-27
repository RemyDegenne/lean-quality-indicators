public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.EvenSporadicStandard.TwoFi22

open scoped Pointwise

variable {G : Type} [Group G]

section Main

variable [Finite G] {t z : G}

theorem Level55.mem_centPair_or_inv_mul_mem (d : Level55 G t z)
    (h54 : IsTwoConstrained (centZ z)) {x : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z) {n : G} (hn : n ∈ normPair z t) :
    n ∈ centPair z t ∨ x⁻¹ * n ∈ centPair z t := by
  have hzz := d.mul_self_z
  obtain ⟨h1, h2⟩ := d.inv_conj_of_swap hxz hxt
  have hnz := d.normPair_conj_z h54 hxz hxt hn
  rcases d.normPair_conj_t h54 hn with h | h
  · left
    rw [mem_centPair_iff]
    exact ⟨(mul_inv_eq_iff_eq_mul.1 hnz).symm, (mul_inv_eq_iff_eq_mul.1 h).symm⟩
  · right
    rw [mem_centPair_iff]
    refine ⟨(mul_inv_eq_iff_eq_mul.1 ?_).symm, (mul_inv_eq_iff_eq_mul.1 ?_).symm⟩
    · calc x⁻¹ * n * z * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * z * n⁻¹) * x := by group
        _ = x⁻¹ * z * x := by rw [hnz]
        _ = z := h1
    · calc x⁻¹ * n * t * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * t * n⁻¹) * x := by group
        _ = x⁻¹ * (t * z) * x := by rw [h]
        _ = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
        _ = t * z * z := by rw [h1, h2]
        _ = t := by rw [mul_assoc, hzz, mul_one]

end Main
end CFSG.EvenSporadicStandard.TwoB
end
