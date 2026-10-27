public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin

section Lift

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem index_normalizer {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) :
    (Subgroup.normalizer (K₁ : Set Γ)).index = 2 := by
  rw [normalizer_eq_ker_chi hπ hK₁ m₁, Subgroup.index_ker, chi_range hπ, Subgroup.card_top,
    W5.card_Q2]

end Lift
end CFSG.Quasithin.He9
end
