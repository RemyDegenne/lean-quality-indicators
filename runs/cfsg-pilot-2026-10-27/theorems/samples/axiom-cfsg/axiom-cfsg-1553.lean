public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct DihedralGroup

open scoped commutatorElement

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem commutator_E64_B₀ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) (hdE : d ∉ E) :
    ⁅E, zpowers d⁆ = zpowers D.b₀ := by
  obtain ⟨-, -, hB₀, -⟩ := D.E64_decomp hE
  obtain ⟨e⟩ := D.B₀_iso
  have hn2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have hz := symm_zc_eq e hn2 D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy
  apply le_antisymm
  · rw [commutator_le]
    intro v hv y hy
    have hyR : y ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G) := (zpowers_le.2 hd) hy
    obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
    rw [D.commutator_eq_B₀ (mem_inf.1 hu).2 (mem_inf.1 hw₀).2 (mem_inf.1 hw₁).2
      (mem_inf.1 hyR).1]
    have hinv := conj_of_mem_inf_normalizer_four e (by omega) hB₀ hyR (inv_mem hw₀)
    rw [hz] at hinv
    rcases hinv with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
      exact mem_zpowers _
  · rw [zpowers_le]
    have hdE' : d ∉ E ⊓ D.B₀ := fun h => hdE (mem_inf.1 h).1
    obtain ⟨v, hv, hvd⟩ := exists_conj_of_not_mem_four e (by omega) hB₀ hd hdE'
    rw [hz] at hvd
    have hb : v * D.b₀ = D.b₀ * v := D.b₀_comm v (mem_inf.1 hv).2
    have hb' : D.b₀⁻¹ = D.b₀ := inv_eq_of_mul_eq_one_right D.b₀_mul_b₀
    have hc : ⁅v, d⁆ = D.b₀ := by
      rw [commutatorElement_def]
      calc v * d * v⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
        _ = v * (v * D.b₀)⁻¹ := by rw [hvd]
        _ = v * D.b₀⁻¹ * v⁻¹ := by group
        _ = D.b₀ := by rw [hb', hb]; group
    rw [← hc]
    exact commutator_mem_commutator (mem_inf.1 hv).1 (mem_zpowers d)

end FooteCore
end CFSG.CGT.Foote81L6
end
