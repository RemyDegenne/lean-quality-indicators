public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

namespace RankTwoSystem

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

variable {D}

theorem IsOpposition.theta_root₁ {τ : X ≃* X} (hτ : D.IsOpposition τ) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) {y : X} (hy : y ∈ D.root 1) :
    ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, τ.trans (MulAut.conj g) y = b * z := by
  obtain ⟨_, V₂, -, -, h₂c, -, n₂, -, -, -, l₃₂, -⟩ := D.exists_layers
  have hz := oppConj_root₁ hτ (D.lift_mk D.w₀) hy
  have hmem : τ.trans (MulAut.conj g) y ∈ V₂ := by
    rw [theta_eq]
    exact n₂ _ hg _ (l₃₂ hz)
  rw [← SetLike.mem_coe, h₂c] at hmem
  obtain ⟨b, hb, z, hz', e⟩ := Set.mem_mul.1 hmem
  exact ⟨b, hb, z, hz', e.symm⟩

end RankTwoSystem
end CFSG.GH74.BNPair
end
