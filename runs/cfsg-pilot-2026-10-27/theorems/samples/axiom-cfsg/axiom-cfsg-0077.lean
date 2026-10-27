public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_CM_t_rho (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hgt : g * t = t * g) (hgρ : g * rho = rho * g) :
    g ∈ closure ({t, tau, rho} : Set G) := by
  have hgτ_mem : g * tau * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) tau := ⟨g, hg, rfl⟩
  rw [hc.tauM] at hgτ_mem
  obtain ⟨v, hvV, hv_eq⟩ := hgτ_mem
  simp only [smul_eq_mul] at hv_eq
  have hρτ : rho * tau * rho⁻¹ = tau := by
    rw [(c13K_rho_comm hc).2.1]; group
  have hgρ' : g⁻¹ * rho⁻¹ = rho⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, hgρ.symm, mul_inv_rev]
  have hconj : rho * (g * tau * g⁻¹) * rho⁻¹ = g * tau * g⁻¹ := by
    calc rho * (g * tau * g⁻¹) * rho⁻¹
        = (rho * g) * tau * (g⁻¹ * rho⁻¹) := by group
      _ = (g * rho) * tau * (rho⁻¹ * g⁻¹) := by rw [hgρ.symm, hgρ']
      _ = g * (rho * tau * rho⁻¹) * g⁻¹ := by group
      _ = g * tau * g⁻¹ := by rw [hρτ]
  have hfix : rho * v * rho⁻¹ = v := by
    have h2 : rho * (tau * v) * rho⁻¹ = tau * v := by
      rw [hv_eq]; exact hconj
    have h3 : rho * (tau * v) * rho⁻¹ = tau * (rho * v * rho⁻¹) := by
      calc rho * (tau * v) * rho⁻¹
          = (rho * tau * rho⁻¹) * (rho * v * rho⁻¹) := by group
        _ = tau * (rho * v * rho⁻¹) := by rw [hρτ]
    rw [h3] at h2
    exact mul_left_cancel h2
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (c13K_four_le_base x₁ x₂ hvV)
  have hv1 : v = 1 := hc.fpf_QY.fix v hvQ hfix
  have hgtau : g * tau * g⁻¹ = tau := by
    rw [← hv_eq, hv1, mul_one]
  have hgtau_comm : g * tau = tau * g := by
    calc g * tau = (g * tau * g⁻¹) * g := by group
      _ = tau * g := by rw [hgtau]
  have hmem_cent : g ∈ centralizer ((closure ({t, tau, rho} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact hgt.symm
    · exact hgtau_comm.symm
    · exact hgρ.symm
  have hg_in : g ∈ ctxM t tau x₁ x₂ ⊓
      centralizer ((closure ({t, tau, rho} : Set G) : Subgroup G) : Set G) := ⟨hg, hmem_cent⟩
  rw [hc.cent_trho] at hg_in
  exact hg_in

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
