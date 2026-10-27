public section

namespace CFSG.ClassicalInvolution.PhanDn

open SimpleGraph CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog

open CFSG.ClassicalInvolution.Phan.Geometry

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_reduce (hσ : IsUnitaryInvolution σ) {u v : FlagVert σ 3}
    (h : (flagGraph σ 3).Adj u v) :
    ∃ q : (compGraph σ).Walk (retractCompVert hσ u) (retractCompVert hσ v),
      CompHedge hσ h q := by
  classical
  by_cases hu : Module.finrank K u.1 = 2
  · by_cases hv : Module.finrank K v.1 = 2
    · exact absurd hv (flagGraph_not_two_two h hu)
    · have hv14 : Module.finrank K v.1 = 1 ∨ Module.finrank K v.1 = 4 := by
        rcases v.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hv
        · exact Or.inr h4
      rcases hv14 with hv1 | hv4
      · have hvu : v.1 < u.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · exact hgt
          · omega
        exact exists_reduce_line_point hσ hu hv1 h hvu
      · have huv : u.1 < v.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · exact hlt
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        exact exists_reduce_line_solid hσ hu hv4 h huv
  · by_cases hv : Module.finrank K v.1 = 2
    · have hu14 : Module.finrank K u.1 = 1 ∨ Module.finrank K u.1 = 4 := by
        rcases u.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hu
        · exact Or.inr h4
      rcases hu14 with hu1 | hu4
      · have huv : u.1 < v.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · exact hlt
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        exact exists_reduce_point_line hσ hu1 hv h huv
      · have hvu : v.1 < u.1 := by
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · exact hgt
          · omega
        exact exists_reduce_solid_line hσ hu4 hv h hvu
    · have hu14 : Module.finrank K u.1 = 1 ∨ Module.finrank K u.1 = 4 := by
        rcases u.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hu
        · exact Or.inr h4
      have hv14 : Module.finrank K v.1 = 1 ∨ Module.finrank K v.1 = 4 := by
        rcases v.finrank_one_two_four (σ := σ) with h1 | h2 | h4
        · exact Or.inl h1
        · exact absurd h2 hv
        · exact Or.inr h4
      rcases hu14 with hu1 | hu4
      · rcases hv14 with hv1 | hv4
        · exfalso
          rcases h with hlt | hgt | ⟨h1, h2, h3⟩
          · have := Submodule.finrank_lt_finrank_of_lt hlt
            omega
          · have := Submodule.finrank_lt_finrank_of_lt hgt
            omega
          · omega
        · exact exists_reduce_retained hσ hu hv h
      · rcases hv14 with hv1 | hv4
        · exact exists_reduce_retained hσ hu hv h
        · exact exists_reduce_retained hσ hu hv h

end CFSG.ClassicalInvolution.PhanDn
end
