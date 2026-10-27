public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_swapper (F : FanTree Γ G) (h40 : Fan40 F) (ℓ : Line Γ) (c : ℤ) {ξ : V}
    (hv3 : valence Γ (ℓ.vert (c + 3)) = 3) (hξ : Γ.Adj (ℓ.vert (c + 3)) ξ)
    (h2 : ξ ≠ ℓ.vert (c + 2)) (h4 : ξ ≠ ℓ.vert (c + 4)) :
    ∃ h : G, h • ℓ.vert c = ℓ.vert c ∧ h • ℓ.vert (c + 2) = ℓ.vert (c + 2) ∧
      h • ℓ.vert (c + 3) = ℓ.vert (c + 3) ∧ h • ℓ.vert (c + 4) = ξ := by
  have hns : ¬ RightSingular Γ G (ℓ.arc c 3).vert 0 3 := fun h =>
    h40 3 (by norm_num) (by norm_num) ⟨ℓ.arc c 3, h⟩
  obtain ⟨X, hX, hX4⟩ := ℓ.exists_fixer_right' c 3 0 3 (by norm_num) hns
  have f0 : X • ℓ.vert c = ℓ.vert c := by simpa using hX c (by norm_num) (by norm_num)
  have f2 : X • ℓ.vert (c + 2) = ℓ.vert (c + 2) := hX _ (by norm_num) (by norm_num)
  have f3 : X • ℓ.vert (c + 3) = ℓ.vert (c + 3) := hX _ (by norm_num) (by norm_num)
  have hX4' : X • ℓ.vert (c + 4) ≠ ℓ.vert (c + 4) := by
    simpa [show c + 3 + 1 = c + 4 by ring] using hX4
  have a34 : Γ.Adj (ℓ.vert (c + 3)) (ℓ.vert (c + 4)) := by
    have := ℓ.adj (c + 3)
    rwa [show c + 3 + 1 = c + 4 by ring] at this
  have a32 : Γ.Adj (ℓ.vert (c + 3)) (ℓ.vert (c + 2)) := by
    have := (ℓ.adj (c + 2)).symm
    rwa [show c + 2 + 1 = c + 3 by ring] at this
  have n24 : ℓ.vert (c + 2) ≠ ℓ.vert (c + 4) := by
    have := ℓ.nb (c + 2)
    rwa [show c + 2 + 2 = c + 4 by ring] at this
  have hadj : Γ.Adj (ℓ.vert (c + 3)) (X • ℓ.vert (c + 4)) := by
    have := (F.adj_smul X _ _).2 a34
    rwa [f3] at this
  rcases P58.eq_of_three hv3 a32 a34 hξ n24 (Ne.symm h2) (Ne.symm h4) hadj with e | e | e
  · exact absurd (MulAction.injective X (show X • ℓ.vert (c + 4) = X • ℓ.vert (c + 2) by
      rw [e, f2])) (fun h => n24 h.symm)
  · exact absurd e hX4'
  · exact ⟨X, f0, f2, f3, e⟩

end P515
end CFSG.Quasithin.Fan86
end
