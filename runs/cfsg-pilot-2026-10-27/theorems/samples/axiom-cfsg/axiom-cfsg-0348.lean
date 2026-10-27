public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big

open scoped commutatorElement

theorem dsa6_orbit {G : Type} [Group G] [Finite G] {Z : Subgroup G} (hZ4 : Nat.card Z = 4) {y : G}
    (hy3 : y * y * y = 1) (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hcy : y * c = c * y) {z : G} (hz : z ∈ Z) : y * z = z * y := by
  by_contra hzy
  set σ : G → G := fun x => y * x * y⁻¹ with hσ
  have hσinj : ∀ a b : G, σ a = σ b → a = b := by
    intro a b h
    simp only [hσ] at h
    have h' := congrArg (fun x => y⁻¹ * x * y) h
    simpa [mul_assoc] using h'
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    simp only [hσ]
    have e : y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x * (y * y * y)⁻¹ := by group
    rw [e, hy3]
    group
  have hσc : σ c = c := by
    simp only [hσ]
    rw [hcy]
    group
  have hσ1 : σ 1 = 1 := by
    simp only [hσ]
    group
  have hσz : σ z ≠ z := by
    intro h
    apply hzy
    simp only [hσ] at h
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [h]
  have hwZ : σ z ∈ Z := hyZ z hz
  have hw2Z : σ (σ z) ∈ Z := hyZ _ hwZ
  have a2 : z ≠ 1 := by
    intro h
    apply hσz
    rw [h, hσ1]
  have a3 : σ z ≠ 1 := by
    intro h
    apply a2
    apply hσinj
    rw [h, hσ1]
  have a4 : σ (σ z) ≠ 1 := by
    intro h
    apply a3
    apply hσinj
    rw [h, hσ1]
  have a5 : z ≠ c := by
    intro h
    apply hσz
    rw [h]
    exact hσc
  have a6 : σ z ≠ c := by
    intro h
    have h2 : σ (σ z) = σ z := by rw [h, hσc]
    apply hσz
    apply hσinj
    rw [h2]
  have a7 : σ (σ z) ≠ c := by
    intro h
    apply a5
    have h3 : σ (σ (σ z)) = σ c := by rw [h]
    rw [hσ3 z, hσc] at h3
    exact h3
  have a8 : σ (σ z) ≠ z := by
    intro h
    apply hσz
    have h3 : σ (σ (σ z)) = σ z := by rw [h]
    rw [hσ3 z] at h3
    exact h3.symm
  have a9 : σ z ≠ σ (σ z) := by
    intro h
    apply hσz
    apply hσinj
    exact h.symm
  have hset : ({1, c, z, σ z, σ (σ z)} : Set G).ncard = 5 := by
    have n1 : (1 : G) ∉ ({c, z, σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hc1 h.symm, fun h => a2 h.symm, fun h => a3 h.symm, fun h => a4 h.symm⟩
    have n2 : c ∉ ({z, σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => a5 h.symm, fun h => a6 h.symm, fun h => a7 h.symm⟩
    have n3 : z ∉ ({σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hσz.symm, fun h => a8 h.symm⟩
    have n4 : σ z ∉ ({σ (σ z)} : Set G) := by
      simp only [Set.mem_singleton_iff]
      exact a9
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_singleton]
  have hsub : ({1, c, z, σ z, σ (σ z)} : Set G) ⊆ (Z : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hc
    · exact hz
    · exact hwZ
    · exact hw2Z
  have hZc : (Z : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ4
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hset, hZc] at this
  omega

end CFSG.GH74.QTGen4.DSGen4
end
