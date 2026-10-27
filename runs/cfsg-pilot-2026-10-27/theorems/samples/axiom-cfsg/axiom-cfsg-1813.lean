public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_gens_mem_O (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    t ∈ ctxO t tau x₁ x₂ ∧ tau ∈ ctxO t tau x₁ x₂ ∧ x₁ ∈ ctxO t tau x₁ x₂ ∧
      x₂ ∈ ctxO t tau x₁ x₂ := by
  obtain ⟨htM, htauM, hx₁M, hx₂M, _, _⟩ :=
    p0_gens_mem_M hc.toCtx10.toCtx4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.O_eq_C]; exact ⟨htM, t_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨htauM, tau_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨hx₁M, x₁_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨hx₂M, x₂_mem_centralizer_fourGrp hc⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
