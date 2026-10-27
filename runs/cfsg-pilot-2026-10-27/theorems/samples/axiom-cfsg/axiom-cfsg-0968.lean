public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.PSL2Table

open scoped MatrixGroups

theorem exists_isPGroup_two_normalized_of_commute {G : Type*} [Group G] {x y z : G}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hzx : z * x * z⁻¹ = y) (hzy : z * y * z⁻¹ = x * y) :
    ∃ V : Subgroup G, IsPGroup 2 V ∧ x ∈ V ∧ z ∈ Subgroup.normalizer (V : Set G) := by
  have hz2 : ∀ t : G, t * t = 1 → IsPGroup 2 (Subgroup.zpowers t) := by
    intro t ht
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers y : Set G) ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq
  have hV : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  set V : Subgroup G := Subgroup.closure ({x, y} : Set G) with hVdef
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hyV : y ∈ V := Subgroup.subset_closure (by simp)
  have key : ∀ g : G, g * x * g⁻¹ ∈ V → g * y * g⁻¹ ∈ V → ∀ h ∈ V, g * h * g⁻¹ ∈ V := by
    intro g hgx hgy h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with rfl | ht
      · exact hgx
      · rw [Set.mem_singleton_iff.mp ht]
        exact hgy
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact V.mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact V.inv_mem ha
  have h1 : z * (x * y) * z⁻¹ = x := by
    calc z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
      _ = y * (x * y) := by rw [hzx, hzy]
      _ = x := by rw [hxy, ← mul_assoc, hy, one_mul]
  have hzx' : z⁻¹ * x * z⁻¹⁻¹ = x * y := by
    calc z⁻¹ * x * z⁻¹⁻¹ = z⁻¹ * (z * (x * y) * z⁻¹) * z⁻¹⁻¹ := by rw [h1]
      _ = x * y := by group
  have hzy' : z⁻¹ * y * z⁻¹⁻¹ = x := by
    calc z⁻¹ * y * z⁻¹⁻¹ = z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ := by rw [hzx]
      _ = x := by group
  refine ⟨V, ?_, hxV, ?_⟩
  · rw [hV]
    exact IsPGroup.to_sup_of_normal_right' (hz2 x hx) (hz2 y hy) hxN
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key z (hzx ▸ hyV) (hzy ▸ V.mul_mem hxV hyV) h, fun hh => ?_⟩
    have := key z⁻¹ (hzx' ▸ V.mul_mem hxV hyV) (hzy' ▸ hxV) _ hh
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankFourTheoremC
end
