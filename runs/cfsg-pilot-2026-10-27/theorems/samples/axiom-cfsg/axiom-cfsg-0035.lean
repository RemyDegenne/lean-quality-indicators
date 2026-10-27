public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem z4i_tauBar_V (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (q : ↥(ctxQ t tau x₁ x₂ rho)) :
    hz.z4iTauBar q * q⁻¹ ∈ z4iV t tau x₁ x₂ rho := by
  rw [z4iV, Subgroup.mem_subgroupOf]
  have h1 : ((hz.z4iTauBar q : ↥(ctxQ t tau x₁ x₂ rho)) : G) = tau * (q : G) * tau⁻¹ := by
    change ((z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ q :
      ↥(ctxQ t tau x₁ x₂ rho)) : G) = tau * (q : G) * tau⁻¹
    rw [z4iPsi_apply_coe]
  have h2 : tau * (q : G) * tau⁻¹ = (q : G)⁻¹ := hz.tau_inv_Q (q : G) q.2
  have hcoe : ((hz.z4iTauBar q * q⁻¹ : ↥(ctxQ t tau x₁ x₂ rho)) : G) = ((q : G)⁻¹) ^ 2 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, h2, pow_two]
  rw [hcoe]
  exact (hz.V_eq_sq (((q : G)⁻¹) ^ 2)).mpr ⟨(q : G)⁻¹, inv_mem q.2, rfl⟩

end Ctx4Z
end CFSG.OddStandard.SmallF3.HarrisU33
end
