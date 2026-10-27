public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits

open CFSG.LieType.Steinberg.TwistedD4

open scoped MatrixGroups

section Main

variable {p : ℕ} [hp : Fact p.Prime] {n e : ℕ}

theorem commutingGeneration_of_degenerate_pair {X : Type*} [Group X] {𝓕 : Set (Subgroup X)}
    {c₁ c₂ : X}
    (h : c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1) (hall : (⊤ : Subgroup X) ≤ ⨆ R ∈ 𝓕, R) :
    (⊤ : Subgroup X) ≤ ⨆ R ∈ 𝓕,
      ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₂} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₁ * c₂} : Set X)), R := by
  refine hall.trans (iSup₂_le fun R hR => le_iSup₂_of_le R hR (le_iSup_of_le ?_ le_rfl))
  have h1 : ∀ x : X, x = 1 → R ≤ Subgroup.centralizer ({x} : Set X) := fun x hx r _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (by simp [hx])
  rcases h with h | h | h
  · exact Or.inl (h1 _ h)
  · exact Or.inr (Or.inl (h1 _ h))
  · exact Or.inr (Or.inr (h1 _ h))

end Main
end CFSG.ClassicalInvolution.ModelFacts
end
