public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Elementary

variable {G : Type} [Group G] {U : Type} [Group U] {Δ : UniversalRootDatum U}

theorem GGRootInvolution.conj {t : StatedLieTag} {ψ : U →* G} {r : G}
    (h : GGRootInvolution Δ t ψ r) (v : U) : GGRootInvolution Δ t ψ (ψ v * r * (ψ v)⁻¹) := by
  obtain ⟨hr, γ, hγ, u, hru⟩ := h
  refine ⟨?_, γ, hγ, v * u, conj_mem_ggRootSub hru v⟩
  have ho := MulEquiv.orderOf_eq (MulAut.conj (ψ v)) r
  rw [MulAut.conj_apply] at ho
  rw [ho, hr]

end Elementary
end CFSG.StandardType
end
