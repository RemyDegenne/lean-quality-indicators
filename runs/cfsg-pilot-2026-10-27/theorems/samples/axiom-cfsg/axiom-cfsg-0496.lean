public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c167_centralizer_cClos_le (D : Data G) {V : Subgroup G} (hVT : V ≤ D.T) {z : G}
    (hz : z ∈ V ⊓ centralizer (D.T : Set G)) (i : ℕ) :
    centralizer (E3.cClos V i D.T : Set G) ≤ centralizer ({z} : Set G) := by
  refine Subgroup.centralizer_le ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  refine Subgroup.mem_inf.2 ⟨hVT hz.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact Subgroup.mem_centralizer_iff.1 hz.2 w (E3.wClos_le i D.T hw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
