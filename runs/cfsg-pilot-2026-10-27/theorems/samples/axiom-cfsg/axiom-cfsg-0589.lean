public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z : G} {f : ↥K →* GL32}

theorem Data619.mem_sup_of_mem_Inn (h : Data619 M B H S K z f) {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K),
      (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : ↥S} (ha : Φ a ∈ L32Insp.Inn) : (a : G) ∈ K ⊔ pCoreOf 2 H := by
  obtain ⟨q, hq⟩ := L32Insp.mem_Inn.1 ha
  obtain ⟨k₀, rfl⟩ := h.f_surj q
  have hy : (k₀ : G)⁻¹ * (a : G) ∈ h.centK ⊓ (K ⊔ S) :=
    ⟨h.inv_mul_mem_centK hΦ hq, mul_mem (mem_sup_left (inv_mem k₀.2)) (mem_sup_right a.2)⟩
  have e : (a : G) = (k₀ : G) * ((k₀ : G)⁻¹ * (a : G)) := by group
  rw [e]
  exact mul_mem (mem_sup_left k₀.2) (mem_sup_right (h.D_le_core hy))

end CFSG.LocalAnalysis.RankThreeTheoremC
end
