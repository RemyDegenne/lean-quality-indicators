public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

section Abstract

theorem map_le_closure_pow {G H : Type*} [Group G] [Group H] (f : G →* H) {X : Subgroup G} {r : ℕ}
    (hX : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1}) :
    X.map f ≤ Subgroup.closure {y | y ∈ X.map f ∧ ∃ n : ℕ, y ^ (r ^ n) = 1} := by
  rintro _ ⟨x, hx, rfl⟩
  have h1 := Subgroup.mem_map_of_mem f (hX hx)
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hy, n, hn⟩, rfl⟩
  exact ⟨⟨y, hy, rfl⟩, n, by rw [← map_pow, hn, map_one]⟩

end Abstract
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
end
