public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open CFSG.Quasithin.CosetGeom

open scoped Pointwise

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

namespace HypF98

variable {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem exists_F8Setup_of_critical (h : HypF98 T V L V₁ Vp H) {γ : F8.Geom T L H}
    (hγ : IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ) :
    ∃ (γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g := by
  have hyp := h.amalgamHypV
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  have hodd : Odd (critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V) := h.three_le_b_and_odd.2
  obtain ⟨⟨γ', hγ'nb, hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj γ γ' := SimpleGraph.Adj.symm hγ'nb
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)
  · exact ⟨γ', g, ⟨hγ, hγ'nb, hd', hg0, hg1⟩⟩

end HypF98
end Fin
end CFSG.Quasithin
end
