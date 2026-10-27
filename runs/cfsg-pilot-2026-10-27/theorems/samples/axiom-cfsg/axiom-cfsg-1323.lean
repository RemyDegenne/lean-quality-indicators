public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

theorem t₀_conj_mem_T {x : P} (hx : x ∈ M.T) : M.t₀ * x * M.t₀⁻¹ ∈ M.T := by
  have h := M.conj_t₀_mem_T (mul_mem (mul_mem M.t₀_sq_mem_T hx) (inv_mem M.t₀_sq_mem_T))
  have e : M.t₀⁻¹ * (M.t₀ * M.t₀ * x * (M.t₀ * M.t₀)⁻¹) * M.t₀ = M.t₀ * x * M.t₀⁻¹ := by group
  rwa [e] at h

end Model
end CFSG.ComponentClassification.GSThmB.P29
end
