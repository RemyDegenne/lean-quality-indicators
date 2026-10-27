public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)

open CFSG.GH74.GLS.IVK.Lifted (gammaOf slFieldAut slFieldAut_apply)

open scoped commutatorElement

section BFCtx2

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H}

theorem comm_mem_of_t (hS : Setting H K₁ K₂ z) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) {t : H}
    (htN : t ∉ normalizer (K₁ : Set H)) {y : H} (hy : y ∈ normalizer (K₁ : Set H))
    (hty : t * y * t⁻¹ * y⁻¹ ∈ K₁ ⊔ K₂) (g : H) : ⁅g, y⁆ ∈ K₁ ⊔ K₂ := by
  have hidx := hS.index_eq_two htN
  by_cases hg : g ∈ normalizer (K₁ : Set H)
  · exact hS.comm_mem h2A7 hg hy
  · have hn : t⁻¹ * g ∈ normalizer (K₁ : Set H) := by
      rcases mem_or_of_index_two (N := normalizer (K₁ : Set H)) hidx htN g with h | h
      · exact absurd h hg
      · exact h
    have hκ := hS.comm_mem h2A7 hn hy
    have e : ⁅g, y⁆ = (t * ⁅t⁻¹ * g, y⁆ * t⁻¹) * (t * y * t⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (K₁ ⊔ K₂).mul_mem (hS.normal.conj_mem _ hκ t) hty

end BFCtx2
end CFSG.GH74.GLS.IVK.Prod3
end
