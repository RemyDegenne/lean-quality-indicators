set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors

section Stability

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {M : Type*}

theorem IsSmoothVector.smul [MulAction G M] [ContinuousMul G] {v : M}
    (hv : IsSmoothVector G v) (g : G) : IsSmoothVector G (g • v) := by
  rw [isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
  have hset : ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
      = (fun h : G => g⁻¹ * h * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
    constructor
    · intro hh
      calc (g⁻¹ * h * g) • v = g⁻¹ • h • g • v := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • g • v := by rw [hh]
        _ = v := inv_smul_smul g v
    · intro hh
      calc h • g • v = g • g⁻¹ • h • g • v := (smul_inv_smul g _).symm
        _ = g • (g⁻¹ * h * g) • v := by rw [mul_smul, mul_smul]
        _ = g • v := by rw [hh]
  rw [hset]
  exact hv.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end Stability
end FLT.SmoothVectors
