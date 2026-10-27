public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Base

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem IsV1.pow_four (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    y₁ ^ 4 = 1 := by
  obtain ⟨-, hyz, hyC, hρ⟩ := hy
  have hv1 : Model.parrottV 1 ^ 4 = 1 := by
    have := Model.orderOf_parrottV (i := 1) le_rfl (by norm_num)
    rw [if_pos (by decide)] at this
    rw [← this]
    exact pow_orderOf_eq_one _
  have hv5 : Model.parrottV 5 ^ 4 = 1 := by
    have := Model.orderOf_parrottV (i := 5) (by norm_num) (by norm_num)
    rw [if_pos (by decide)] at this
    rw [← this]
    exact pow_orderOf_eq_one _
  have hcomm : Model.parrottV 1 * Model.parrottV 5 = Model.parrottV 5 * Model.parrottV 1 :=
    Model.parrottV_commute le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
  have hρ4 : (d.ρ ⟨y₁, hyC⟩ : Equiv.Perm (Fin 1755)) ^ 4 = 1 := by
    rcases hρ with h | h
    · rw [h]
      exact hv1
    · rw [h, (Commute.mul_pow (show Commute (Model.parrottV 1) (Model.parrottV 5) from hcomm)),
        hv1, hv5, one_mul]
  have hC4 : y₁ ^ 4 ∈ centralizer ({d.t} : Set G) := pow_mem hyC 4
  have hρ' : (d.ρ ⟨y₁ ^ 4, hC4⟩ : Equiv.Perm (Fin 1755)) = 1 := by
    have : (⟨y₁ ^ 4, hC4⟩ : centralizer ({d.t} : Set G)) = ⟨y₁, hyC⟩ ^ 4 := rfl
    rw [this, map_pow]
    exact hρ4
  have h1D : (d.ρ ⟨y₁ ^ 4, hC4⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    rw [hρ']
    exact one_mem _
  rcases hd.eq_lift_or hC4 h1D with h | h
  · rw [hρ', d.lift_one] at h
    exact h
  · rw [hρ', d.lift_one, mul_one] at h
    exfalso
    have hc : y₁ ^ 4 * z₀ = z₀ * y₁ ^ 4 :=
      (Commute.pow_left (show Commute y₁ z₀ from hyz) 4).eq
    rw [h] at hc
    exact t_not_comm_z0 hd hz hc

end Base
end CFSG.LocalAnalysis.EvenBN.Tits.N
end
