public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction

open scoped Pointwise

theorem mem_normalizer_iff_tables {z : M22} {n : ℕ} (hz : orderOf z = n) {zt : Array ℕ}
    (hzt : ⇑(z : Equiv.Perm (Fin 22)) = ofTable zt) {T : Array (Array ℕ)}
    (hT : ∀ j : Fin n, ∀ x, ofTable T[j.val]! x = (ofTable zt)^[j] x) (g : M22) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set M22) ↔
      ∃ j : Fin n, ∀ x, (g : Equiv.Perm (Fin 22)) (ofTable zt x) =
        ofTable T[j.val]! ((g : Equiv.Perm (Fin 22)) x) := by
  rw [mem_normalizer_zpowers_iff, mem_zpowers_iff_mem_range_orderOf, hz, Finset.mem_image]
  have key : ∀ j : ℕ, z ^ j = g * z * g⁻¹ ↔ ∀ x, (g : Equiv.Perm (Fin 22)) (ofTable zt x) =
      (ofTable zt)^[j] ((g : Equiv.Perm (Fin 22)) x) := by
    intro j
    rw [eq_mul_inv_iff_mul_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, Equiv.ext_iff]
    simp only [Equiv.Perm.mul_apply, Subgroup.coe_pow, Equiv.Perm.coe_pow, hzt]
    exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩
  constructor
  · rintro ⟨j, hj, e⟩
    rw [Finset.mem_range] at hj
    refine ⟨⟨j, hj⟩, fun x => ?_⟩
    rw [hT, (key j).1 e x]
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_range.2 j.2, (key j).2 fun x => ?_⟩
    rw [hj x, hT]

end CFSG.ComponentClassification.WittDesign
end
