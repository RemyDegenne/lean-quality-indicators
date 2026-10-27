public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

open CFSG.Assembly.LowTwoRank (StatedSL)

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem mem_V1_of_fixed_inf (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {w : G} (hw : w ∈ fsuV T I)
    (hfix : ∀ t ∈ T ⊓ L, t * w * t⁻¹ = w) : w ∈ V₁ :=
  mem_V1_of_fixed_pCoreOf hF h1102 h hU hw fun r hr =>
    hfix r ⟨ROf_le_T h (pCoreOf_lOf_le_ROf h hU hr),
      lOf_le_L (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr)⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
end
