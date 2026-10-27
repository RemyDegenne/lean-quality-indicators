public section

open scoped commutatorElement

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.LieType.Universal

namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

section Levi

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)

include h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne

theorem levi_eq_sup : levi R A A₀ = gen Δ₁ ⊔ gen Δ₂ := by
  refine le_antisymm (levi_le_sup_of_card_two h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne)
    (sup_le (Sec9.gen_le_levi fun _ hX => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX)
      (Sec9.gen_le_levi fun _ hX => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX))

end Levi
end CaseOA
end CFSG.Timmesfeld.ARS
end
