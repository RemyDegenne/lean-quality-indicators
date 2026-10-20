public section

noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

variable {ϖ : 𝒪[L]} {i : ℕ} {σ : G}

theorem mem_unitFiltration_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {y : Lˣ}
    (hy : (y : L) = σ • (ϖ : L) / (ϖ : L)) : y ∈ unitFiltration L i := by
  have hϖpos : 0 < valuation L (ϖ : L) := by
    simpa using Valuation.integer.v_irreducible_pos (v := valuation L) hϖ
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine (mem_unitFiltration_iff_valuation_le hϖ).mpr ⟨?_, ?_⟩
  · rw [hy, map_div₀, valuation_smul_of_irreducible hϖ σ, div_self hϖpos.ne']
  · rw [hy, div_sub_one hϖne, map_div₀, div_le_iff₀ hϖpos, ← pow_succ]
    exact (mem_ramificationGroup_natCast_iff_valuation_le hϖ).mp hσ ϖ

end TauCeti
end
end
