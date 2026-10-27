public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU

open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem mem_normalizer_of_forall {K : Subgroup G} {w : G} (h : ∀ k ∈ K, w * k * w⁻¹ ∈ K) :
    w ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj w).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥K ≤ Nat.card ↥(K.map (MulAut.conj w).toMonoidHom) :=
    (card_map_conj K w).ge
  have := Subgroup.eq_of_le_of_card_ge hle hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this

end CFSG.GH74.GLS.LU.Local
end
