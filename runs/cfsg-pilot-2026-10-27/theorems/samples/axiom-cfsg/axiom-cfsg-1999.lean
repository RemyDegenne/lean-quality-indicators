public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section Decomp

variable {K : Type*} [Group K] [Finite K]

theorem lemma2_trivial_center {N Lb : Subgroup K} [N.Normal] (hLb : Lb ≤ N)
    (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hZ : ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1)
    (hT2 : ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹)
    {e x : K} (he : e ∈ Lb) (he3 : orderOf e = 3) (hx3 : orderOf x = 3) (hex : e * x = x * e)
    (hxL : x ∉ Subgroup.normalizer (Lb : Set K)) : x ∈ N := by
  have hx : x ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← hx3]
    exact pow_orderOf_eq_one x
  obtain ⟨g, hg, c, hcN, hxgc, -, hg3, hc3⟩ := three_element_decomp hZ hT2 hx
  by_cases hc1 : c = 1
  · rw [hxgc, hc1, mul_one]; exact hg
  exfalso
  have hcnN : c ∉ N := fun h => hc1 (hZ c h hcN)
  have heg : e * g = g * e := by
    have h1 : e * (g * c) = (g * c) * e := by rw [← hxgc]; exact hex
    have hce : c * e = e * c := hcN e (hLb he)
    have : e * g * c = g * e * c := by
      calc e * g * c = e * (g * c) := by group
        _ = g * c * e := h1
        _ = g * (c * e) := by group
        _ = g * (e * c) := by rw [hce]
        _ = g * e * c := by group
    exact mul_right_cancel this
  have hxa : ∀ a ∈ N, x * a * x⁻¹ = g * a * g⁻¹ := by
    intro a ha
    have hca : c * a = a * c := hcN a ha
    calc x * a * x⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by rw [hxgc]; group
      _ = g * a * g⁻¹ := by rw [hca]; group
  by_cases hge : g ∈ Subgroup.zpowers e
  · apply hxL
    have hgLb : g ∈ Lb := (Subgroup.zpowers_le.mpr he) hge
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have haLb : a ∈ Lb := ha
    show x * a * x⁻¹ ∈ Lb
    rw [hxa a (hLb haLb)]
    exact Lb.mul_mem (Lb.mul_mem hgLb haLb) (Lb.inv_mem hgLb)
  · have hg1 : g ≠ 1 := fun h => hge (h ▸ Subgroup.one_mem _)
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    obtain ⟨hE1, -⟩ := isElemAbelian_zpowers_order_three he3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨hE2, hE2c⟩ := exists_elemAbelian_sup_zpowers hE1 hgo (fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (show Commute e g from heg).zpow_left k) hge
    have hE2N : Subgroup.zpowers e ⊔ Subgroup.zpowers g ≤ N :=
      sup_le (Subgroup.zpowers_le.mpr (hLb he)) (Subgroup.zpowers_le.mpr hg)
    have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hcard : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers g) = 9 := by
      rw [hE2c, (isElemAbelian_zpowers_order_three he3).2]
    obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_card_27 hE2 hcard hc3'
      (fun u hu => (show Commute u c from (hcN u (hE2N hu)).symm)) (fun h => hcnN (hE2N h))
    have := hrank A hA
    omega

end Decomp
end Stellmacher.L3YC
end CFSG.Quasithin
end
