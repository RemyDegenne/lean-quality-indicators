public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace TwinConnT

variable {G : Type} [Group G] [Finite G]

theorem liftUnique_in {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {J L₁ L₂ : Subgroup G} {t : G}
    (hJ : J ∈ Ω) (hz : IsUniqueInvolution J t) (hJ₁ : J ≤ L₁) (hJ₂ : J ≤ L₂)
    (h₁ : IsClassicalMember3 L₁ t) (h₂ : IsClassicalMember3 L₂ t)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥) : L₁ = L₂ := by
  have hint : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
    oddCoreIn_eq_bot_of_classicalOddCore hO
  have hi : ∀ L : Subgroup G, Uniform.IsIntrinsicU (.sl2 3 1) L t := by
    intro L _
    rw [hint]
    exact bot_le
  exact eq_of_isLiftOf hΩ hJ ⟨hz, hJ₁, h₁⟩ ⟨hz, hJ₂, h₂⟩ (hi _) (hi _)

end TwinConnT
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
end
