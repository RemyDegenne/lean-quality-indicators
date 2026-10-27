public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Levi

section Quot

variable (h : Hyp G R) {A A₀ E₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hE₀ : E₀ ∈ leviSet R A A₀)

include h hA hAne hA₀ hE₀

theorem card_quot_lt :
    Nat.card (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀))) <
      Nat.card G := by
  have := h.finite
  refine LeviQuot.card_lt fun htop => h.root.ne_bot A hA ?_
  have hle : gen (comp R A A₀ E₀) ≤ levi R A A₀ := gen_mono (comp_subset h hA hAne hA₀ hE₀)
  have hbot := M_inf_levi_eq_bot h hA hA₀
  rw [htop, top_le_iff] at hle
  rw [hle, inf_top_eq] at hbot
  rw [← le_bot_iff, ← hbot]
  exact QD.le_M_self

end Quot
end Levi
end CFSG.Timmesfeld.ARS
end
